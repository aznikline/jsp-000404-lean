import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
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
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h10, h12, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h10, h16, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h10, h18, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h10, h21, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h20, h21, h23, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                                    · linarith only [h16, h20, h21, h26, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h10, h26, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h10, h20, h21, h25, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                              · linarith only [h20, h30, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                                · linarith only [h0, h20, h32, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                                  · linarith only [h10, h20, h34, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h10, h34, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h0, h39, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h38, h39, hc25, hlam, hphi, u2ehi3]
                        · linarith only [h37, h38, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                        · linarith only [h37, h43, hc23, hlam, hphi, u2ehi3]
                        · linarith only [h43, h5, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h46, h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                          · linarith only [h0, h50, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h48, h50, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h48, h49, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h48, h8, hc35, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h55, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h0, h60, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h58, h60, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h58, h59, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h58, h7, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                          · linarith only [h0, h67, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h65, h67, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h65, h66, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h57, h65, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
            · linarith only [h4, h74, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h76 | h76
              · linarith only [h4, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
                · rcases m.htr 0 3 5 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h4, h81, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h0, h74, h80, h83, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h0, h76, h85, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                              · linarith only [h1, h88, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h4, h79, h81, h88, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h4, h78, h81, h87, hc23, hlam, hphi, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                      · linarith only [h4, h79, h92, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                        · linarith only [h0, h74, h94, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                          · linarith only [h0, h76, h96, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                              · linarith only [h1, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · linarith only [h4, h79, h92, h99, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h4, h78, h92, h98, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h103, h78, h79, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                      · linarith only [h0, h105, h74, h78, h79, hc35, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                        · linarith only [h0, h107, h74, h78, h79, hc35, hlam, hphi, ht23, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                          · linarith only [h0, h109, h76, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                              · linarith only [h1, h112, h79, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h114 | h114
                                · linarith only [h103, h114, h2, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                                    · linarith only [h0, h117, h74, h78, h79, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h117, h4, hc35, hlam, hphi, ht23, u2ehi1]
                                  · linarith only [h0, h1, h111, h116, h4, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h111, h78, h79, hc13, hc35, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
                  · linarith only [h122, h78, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
                      · linarith only [h0, h125, h76, hc25, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                        · linarith only [h0, h127, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                          · linarith only [h0, h129, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                            · linarith only [h1, h131, h78, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                              · linarith only [h1, h122, h133, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                                · linarith only [h135, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h124, h127, h135, h74, hc24, hlam, hphi, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                      · linarith only [h0, h124, h138, h4, h78, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                        · linarith only [h0, h124, h140, h4, h78, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h0, h142, h76, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                            · linarith only [h1, h144, h78, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                              · linarith only [h1, h122, h146, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                                · linarith only [h124, h148, h2, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                                  · linarith only [h0, h150, h4, h78, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h150, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
          · rcases m.htr 0 2 4 (by decide) (by decide) with h154 | h154
            · rcases m.htr 0 2 5 (by decide) (by decide) with h155 | h155
              · linarith only [h0, h155, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h153, h155, hc25, hlam, hphi, u2ehi2]
            · linarith only [h153, h154, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h159 | h159
            · linarith only [h153, h159, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
              · linarith only [h153, h161, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                  · linarith only [h1, h164, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h166 | h166
                    · linarith only [h163, h164, h166, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                      · linarith only [h0, h168, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
                        · linarith only [h1, h159, h168, h170, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                          · linarith only [h0, h153, h161, h172, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · linarith only [h1, h168, h172, h3, hc25, hlam, hphi, u2ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h175 | h175
                  · linarith only [h163, h175, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                    · linarith only [h177, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                      · linarith only [h0, h153, h179, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                        · linarith only [h0, h159, h181, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                          · linarith only [h1, h179, h183, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · linarith only [h1, h179, h183, h3, hc25, hlam, hphi, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h186 | h186
        · linarith only [h186, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h188 | h188
          · rcases m.htr 0 2 4 (by decide) (by decide) with h189 | h189
            · linarith only [h0, h189, h2, hlam]
            · linarith only [h188, h189, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h192 | h192
            · linarith only [h188, h192, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h194 | h194
              · linarith only [h188, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h196 | h196
                · linarith only [h1, h196, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h198 | h198
                  · linarith only [h196, h198, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
                      · linarith only [h0, h2, h201, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                        · linarith only [h1, h192, h2, h200, h201, h203, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h1, h2, h201, h203, hc24, hlam, hphi, u2ehi1]
                    · linarith only [h0, h2, h200, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h207 | h207
      · rcases m.htr 0 1 5 (by decide) (by decide) with h208 | h208
        · linarith only [h1, h208, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h210 | h210
          · linarith only [h0, h1, h210, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h212 | h212
            · linarith only [h210, h212, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h214 | h214
              · linarith only [h210, h214, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h216 | h216
                · rcases m.htr 0 3 5 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
                    · linarith only [h1, h207, h218, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                      · linarith only [h0, h1, h220, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h1, h220, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h217, hc35, hlam, hphi, ht23, u2ehi1]
                · linarith only [h0, h1, h216, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h225 | h225
        · linarith only [h1, h225, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h227 | h227
          · linarith only [h0, h1, h227, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
            · linarith only [h227, h229, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h231 | h231
              · linarith only [h227, h231, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h233 | h233
                · rcases m.htr 0 3 5 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h1, h227, h236, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h1, h236, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h207, h235, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h0, h207, h233, h234, hc35, hlam, hphi, ht23, u2ehi1]
                · linarith only [h0, h1, h233, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h242 | h242
    · rcases m.htr 0 1 4 (by decide) (by decide) with h243 | h243
      · rcases m.htr 0 1 5 (by decide) (by decide) with h244 | h244
        · linarith only [h0, h244, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h246 | h246
          · rcases m.htr 0 2 4 (by decide) (by decide) with h247 | h247
            · rcases m.htr 0 2 5 (by decide) (by decide) with h248 | h248
              · rcases m.htr 0 3 4 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
                  · linarith only [h0, h242, h250, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                    · linarith only [h249, h250, h252, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                              · linarith only [h242, h244, h250, h256, h258, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h242, h244, h255, h257, h258, hc35, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h249, h250, h257, hc13, hc35, hlam, hphi]
                          · linarith only [h0, h248, h256, hlam]
                        · linarith only [h0, h248, h255, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h242, h246, h254, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
                  · linarith only [h249, h265, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                    · linarith only [h0, h243, h267, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                            · linarith only [h242, h244, h249, h271, h272, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                              · linarith only [h243, h244, h265, h271, h272, h274, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · linarith only [h243, h244, h269, h272, h274, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h0, h242, h269, h271, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h242, h269, h270, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h248, h269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h246, h248, hc25, hlam, hphi, u2ehi2]
            · linarith only [h246, h247, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h242, h246, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h283 | h283
        · linarith only [h0, h283, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h285 | h285
          · rcases m.htr 0 2 4 (by decide) (by decide) with h286 | h286
            · rcases m.htr 0 2 5 (by decide) (by decide) with h287 | h287
              · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
                · linarith only [h242, h243, h288, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h288, h290, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h294 | h294
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h295 | h295
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                            · linarith only [h242, h243, h288, h294, h296, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h242, h243, h293, h296, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h242, h243, h293, h294, h295, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h242, h286, h293, h294, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h287, h293, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                      · linarith only [h242, h243, h292, h302, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h287, h302, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h286, h287, hc25, hlam, hphi, u2ehi3]
            · linarith only [h285, h286, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h242, h285, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h308 | h308
      · rcases m.htr 0 1 5 (by decide) (by decide) with h309 | h309
        · linarith only [h0, h309, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h311 | h311
          · rcases m.htr 0 2 4 (by decide) (by decide) with h312 | h312
            · rcases m.htr 0 2 5 (by decide) (by decide) with h313 | h313
              · rcases m.htr 0 3 4 (by decide) (by decide) with h314 | h314
                · rcases m.htr 0 3 5 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
                    · linarith only [h0, h308, h316, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                                · linarith only [h308, h309, h316, h318, h322, h323, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h308, h309, h319, h323, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                              · linarith only [h242, h308, h315, h319, h322, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h242, h308, h319, h321, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h242, h308, h313, h318, h319, h320, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h313, h319, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h311, h318, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h242, h308, h331, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                        · linarith only [h242, h308, h315, h334, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h311, h334, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h313, h333, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h242, h308, h314, hlam]
              · linarith only [h311, h313, hc25, hlam, hphi, u2ehi2]
            · linarith only [h311, h312, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h341 | h341
            · linarith only [h311, h341, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h308, h341, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h344 | h344
        · linarith only [h0, h344, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h346 | h346
          · rcases m.htr 0 2 4 (by decide) (by decide) with h347 | h347
            · rcases m.htr 0 2 5 (by decide) (by decide) with h348 | h348
              · rcases m.htr 0 3 4 (by decide) (by decide) with h349 | h349
                · rcases m.htr 0 3 5 (by decide) (by decide) with h350 | h350
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h357 | h357
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                                    · linarith only [h346, h359, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h361 | h361
                                      · linarith only [h242, h350, h352, h358, h359, h361, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                                        · linarith only [h242, h350, h352, h358, h359, h361, h363, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                        · rcases h1bigk with h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h0, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h242, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h308, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h344, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 1) (by simp) with h371 | h371
                                            · linarith only [h371, hlam, p365_0]
                                            · rcases p365_3 (m.d 1 2) (by simp) with h373 | h373
                                              · rcases p365_3 (m.d 1 3) (by simp) with h374 | h374
                                                · linarith only [h352, h374, hlam]
                                                · linarith only [h242, h374, hlam]
                                              · linarith only [h373, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h355, h357, hc12, hlam, hphi, ht01, ht0b, ht5b, p365_1, u5ehi1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h308, h351, h359, h363, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p365_1, u2ehi2]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h344, h351, h359, h363, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p365_1, u2ehi2]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 1) (by simp) with h382 | h382
                                            · linarith only [h382, hlam, p365_0]
                                            · rcases p365_3 (m.d 1 2) (by simp) with h384 | h384
                                              · rcases p365_3 (m.d 1 3) (by simp) with h385 | h385
                                                · rcases p365_3 (m.d 1 4) (by simp) with h386 | h386
                                                  · linarith only [h355, h386, hlam]
                                                  · linarith only [h308, h386, hlam]
                                                · linarith only [h385, hlam, p365_0]
                                              · linarith only [h0, h384, hlam]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h352, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h308, h351, h358, h359, h363, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p365_1, u2ehi3]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h344, h351, h352, h358, h359, h363, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p365_1, u2ehi3]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 1) (by simp) with h395 | h395
                                            · linarith only [h395, hlam, p365_0]
                                            · rcases p365_3 (m.d 1 2) (by simp) with h397 | h397
                                              · rcases p365_3 (m.d 1 3) (by simp) with h398 | h398
                                                · rcases p365_3 (m.d 1 4) (by simp) with h399 | h399
                                                  · rcases p365_3 (m.d 1 5) (by simp) with h400 | h400
                                                    · linarith only [h357, h400, hlam]
                                                    · linarith only [h344, h400, hlam]
                                                  · linarith only [h399, hlam, p365_0]
                                                · linarith only [h242, h398, hlam]
                                              · linarith only [h0, h397, hlam]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h353, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h355, hlam, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h344, h351, h358, h359, h363, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p365_1, u2ehi3]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 1) (by simp) with h410 | h410
                                            · linarith only [h410, hlam, p365_0]
                                            · rcases p365_3 (m.d 1 2) (by simp) with h412 | h412
                                              · rcases p365_3 (m.d 1 3) (by simp) with h413 | h413
                                                · rcases p365_3 (m.d 1 4) (by simp) with h414 | h414
                                                  · rcases p365_3 (m.d 1 5) (by simp) with h415 | h415
                                                    · rcases h4bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h308, hlam, p416_1]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        rcases p416_3 (m.d 0 4) (by simp) with h419 | h419
                                                        · rcases p416_3 (m.d 1 4) (by simp) with h420 | h420
                                                          · rcases p416_3 (m.d 2 4) (by simp) with h421 | h421
                                                            · linarith only [h347, h421, hlam]
                                                            · rcases p416_3 (m.d 3 4) (by simp) with h423 | h423
                                                              · linarith only [h349, h423, hlam]
                                                              · rcases p416_3 (m.d 4 5) (by simp) with h425 | h425
                                                                · linarith only [h351, h425, hlam]
                                                                · linarith only [h361, h425, hlam]
                                                          · linarith only [h353, h420, hlam]
                                                        · linarith only [h347, h419, hlam]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h351, h358, h359, h363, hlam, p416_2]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h358, h359, h363, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p416_1, u2ehi3]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h351, h352, h355, h358, h359, h363, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p416_1, u2ehi3]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        rcases p416_3 (m.d 0 4) (by simp) with h434 | h434
                                                        · linarith only [h308, h434, hlam]
                                                        · linarith only [h347, h434, hlam]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h308, h351, h358, h359, h363, hlam, p416_2]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h358, h359, h363, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p416_1, u2ehi3]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h347, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h353, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h351, h358, h359, h363, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p416_1]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h361, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h349, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h355, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h358, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h363, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h351, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h357, hlam, p416_0]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [h308, h351, h352, h355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p416_1, u2ehi3]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        rcases p416_3 (m.d 0 4) (by simp) with h452 | h452
                                                        · rcases p416_3 (m.d 1 4) (by simp) with h453 | h453
                                                          · rcases p416_3 (m.d 2 4) (by simp) with h454 | h454
                                                            · linarith only [h361, h454, hlam]
                                                            · linarith only [h358, h454, hlam]
                                                          · linarith only [h355, h453, hlam]
                                                        · linarith only [h349, h452, hlam]
                                                      · have p416_0 := h416c.1
                                                        have p416_1 := h416c.2.1
                                                        have p416_2 := h416c.2.2.1
                                                        have p416_3 := h416c.2.2.2
                                                        linarith only [hlam, p416_0]
                                                    · linarith only [h415, hlam, p365_0]
                                                  · linarith only [h308, h414, hlam]
                                                · linarith only [h242, h413, hlam]
                                              · linarith only [h0, h412, hlam]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h354, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h356, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h357, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                                    · linarith only [h358, h468, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h470 | h470
                                      · linarith only [h0, h347, h470, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                                        · linarith only [h0, h346, h349, h358, h470, h472, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                        · linarith only [h358, h472, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h308, h351, h357, hlam]
                              · linarith only [h308, h351, h355, h356, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h242, h349, h355, hlam]
                          · linarith only [h0, h346, h349, h351, h354, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h0, h347, h353, hlam]
                      · linarith only [h0, h346, h352, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h482 | h482
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h483 | h483
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h484 | h484
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h486 | h486
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                                    · linarith only [h346, h488, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h490 | h490
                                      · linarith only [h350, h351, h487, h488, h490, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h492 | h492
                                        · linarith only [h350, h351, h487, h488, h492, hlam]
                                        · rcases h1bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h0, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h242, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h308, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h344, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            rcases p494_3 (m.d 0 1) (by simp) with h500 | h500
                                            · linarith only [h500, hlam, p494_0]
                                            · rcases p494_3 (m.d 1 2) (by simp) with h502 | h502
                                              · rcases p494_3 (m.d 1 3) (by simp) with h503 | h503
                                                · linarith only [h481, h503, hlam]
                                                · linarith only [h242, h503, hlam]
                                              · linarith only [h502, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h351, h484, h486, hc12, hlam, hphi, ht01, ht0b, ht5b, p494_1, u5ehi0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h350, h351, h486, h487, h488, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi3]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p494_1, u5ehi1]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            rcases p494_3 (m.d 0 1) (by simp) with h511 | h511
                                            · linarith only [h511, hlam, p494_0]
                                            · rcases p494_3 (m.d 1 2) (by simp) with h513 | h513
                                              · rcases p494_3 (m.d 1 3) (by simp) with h514 | h514
                                                · rcases p494_3 (m.d 1 4) (by simp) with h515 | h515
                                                  · linarith only [h484, h515, hlam]
                                                  · linarith only [h308, h515, hlam]
                                                · linarith only [h514, hlam, p494_0]
                                              · linarith only [h0, h513, hlam]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h481, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h350, h351, h486, h487, h488, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi3]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h350, h351, h481, h486, h487, h488, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi3]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            rcases p494_3 (m.d 0 1) (by simp) with h524 | h524
                                            · linarith only [h524, hlam, p494_0]
                                            · rcases p494_3 (m.d 1 2) (by simp) with h526 | h526
                                              · rcases p494_3 (m.d 1 3) (by simp) with h527 | h527
                                                · rcases p494_3 (m.d 1 4) (by simp) with h528 | h528
                                                  · rcases p494_3 (m.d 1 5) (by simp) with h529 | h529
                                                    · linarith only [h486, h529, hlam]
                                                    · linarith only [h344, h529, hlam]
                                                  · linarith only [h528, hlam, p494_0]
                                                · linarith only [h242, h527, hlam]
                                              · linarith only [h0, h526, hlam]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h482, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h484, hlam, p494_1]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h350, h351, h486, h487, h488, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p494_1, u2ehi3]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            rcases p494_3 (m.d 0 1) (by simp) with h539 | h539
                                            · linarith only [h539, hlam, p494_0]
                                            · rcases p494_3 (m.d 1 2) (by simp) with h541 | h541
                                              · rcases p494_3 (m.d 1 3) (by simp) with h542 | h542
                                                · rcases p494_3 (m.d 1 4) (by simp) with h543 | h543
                                                  · rcases p494_3 (m.d 1 5) (by simp) with h544 | h544
                                                    · rcases h4bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h308, hlam, p545_1]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h351, hc45, hlam, hphi, ht23, ht34, p545_1, u2ehi3]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h351, hc34, hc45, hlam, hphi, p545_1]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h351, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        rcases p545_3 (m.d 0 4) (by simp) with h551 | h551
                                                        · linarith only [h308, h551, hlam]
                                                        · rcases p545_3 (m.d 1 4) (by simp) with h553 | h553
                                                          · rcases p545_3 (m.d 2 4) (by simp) with h554 | h554
                                                            · linarith only [h482, h554, hlam]
                                                            · rcases p545_3 (m.d 3 4) (by simp) with h556 | h556
                                                              · linarith only [h484, h556, hlam]
                                                              · rcases p545_3 (m.d 4 5) (by simp) with h558 | h558
                                                                · linarith only [h486, h558, hlam]
                                                                · linarith only [h351, h558, hlam]
                                                          · linarith only [h308, h553, hlam]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        rcases p545_3 (m.d 0 4) (by simp) with h563 | h563
                                                        · linarith only [h308, h563, hlam]
                                                        · linarith only [h347, h563, hlam]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h350, h351, h486, h487, h488, hlam, p545_2]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h347, h351, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p545_1, u2ehi3]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h347, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h482, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h347, h351, h481, h484, h486, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h490, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h349, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h484, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h487, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h492, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h347, h481, h484, h486, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p545_1, u2ehi3]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h486, hlam, p545_0]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [h481, h484, h486, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p545_1, u2ehi3]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        rcases p545_3 (m.d 0 4) (by simp) with h581 | h581
                                                        · linarith only [h351, h581, hlam]
                                                        · linarith only [h349, h581, hlam]
                                                      · have p545_0 := h545c.1
                                                        have p545_1 := h545c.2.1
                                                        have p545_2 := h545c.2.2.1
                                                        have p545_3 := h545c.2.2.2
                                                        linarith only [hlam, p545_0]
                                                    · linarith only [h544, hlam, p494_0]
                                                  · linarith only [h308, h543, hlam]
                                                · linarith only [h242, h542, hlam]
                                              · linarith only [h0, h541, hlam]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h483, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h485, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [h486, hlam, p494_0]
                                          · have p494_0 := h494c.1
                                            have p494_1 := h494c.2.1
                                            have p494_2 := h494c.2.2.1
                                            have p494_3 := h494c.2.2.2
                                            linarith only [hlam, p494_0]
                                  · linarith only [h349, h351, h481, h484, h486, h487, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h594 | h594
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h595 | h595
                                    · linarith only [h0, h346, h595, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h597 | h597
                                      · linarith only [h308, h486, h597, hc01, hc24, hlam, hphi, ht12]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                                        · linarith only [h242, h308, h350, h481, h486, h594, h595, h599, hc01, hc12, hlam, hphi]
                                        · rcases h1bigk with h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h0, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h242, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h308, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h344, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            rcases p601_3 (m.d 0 1) (by simp) with h607 | h607
                                            · linarith only [h607, hlam, p601_0]
                                            · rcases p601_3 (m.d 1 2) (by simp) with h609 | h609
                                              · rcases p601_3 (m.d 1 3) (by simp) with h610 | h610
                                                · linarith only [h481, h610, hlam]
                                                · linarith only [h242, h610, hlam]
                                              · linarith only [h609, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h242, h350, h594, h595, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p601_1, u2ehi3]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h308, hc01, hc12, hlam, hphi, p601_1]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h344, hc12, hlam, hphi, ht01, ht0b, ht5b, p601_1, u5ehi0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            rcases p601_3 (m.d 0 1) (by simp) with h618 | h618
                                            · linarith only [h618, hlam, p601_0]
                                            · rcases p601_3 (m.d 1 2) (by simp) with h620 | h620
                                              · rcases p601_3 (m.d 1 3) (by simp) with h621 | h621
                                                · rcases p601_3 (m.d 1 4) (by simp) with h622 | h622
                                                  · linarith only [h484, h622, hlam]
                                                  · linarith only [h308, h622, hlam]
                                                · linarith only [h621, hlam, p601_0]
                                              · linarith only [h0, h620, hlam]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h481, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h308, hc01, hc13, hlam, hphi, p601_1]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h344, h350, h481, h594, h595, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p601_1, u2ehi3]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h486, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p601_1]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h482, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h484, hlam, p601_1]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h486, hlam, p601_1]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            rcases p601_3 (m.d 0 1) (by simp) with h636 | h636
                                            · linarith only [h636, hlam, p601_0]
                                            · rcases p601_3 (m.d 1 2) (by simp) with h638 | h638
                                              · rcases p601_3 (m.d 1 3) (by simp) with h639 | h639
                                                · rcases p601_3 (m.d 1 4) (by simp) with h640 | h640
                                                  · linarith only [h486, h640, hlam]
                                                  · linarith only [h308, h640, hlam]
                                                · linarith only [h242, h639, hlam]
                                              · linarith only [h0, h638, hlam]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h483, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h485, hlam, p601_0]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [h308, hc01, hc15, hlam, hphi, p601_1]
                                          · have p601_0 := h601c.1
                                            have p601_1 := h601c.2.1
                                            have p601_2 := h601c.2.2.1
                                            have p601_3 := h601c.2.2.2
                                            linarith only [hlam, p601_0]
                                  · linarith only [h349, h351, h594, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h242, h350, h485, hlam]
                            · linarith only [h242, h349, h350, h351, h484, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · linarith only [h0, h346, h350, h483, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h346, h350, h482, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h346, h350, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
                    · linarith only [h349, h350, h655, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h661 | h661
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h662 | h662
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h663 | h663
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
                                    · linarith only [h346, h350, h664, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                                      · linarith only [h347, h655, h666, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                                        · linarith only [h346, h350, h655, h657, h661, h663, h668, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                        · rcases h1bigk with h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c | h670c
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h0, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h242, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h308, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h344, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            rcases p670_3 (m.d 0 1) (by simp) with h676 | h676
                                            · linarith only [h676, hlam, p670_0]
                                            · rcases p670_3 (m.d 1 2) (by simp) with h678 | h678
                                              · rcases p670_3 (m.d 1 3) (by simp) with h679 | h679
                                                · linarith only [h657, h679, hlam]
                                                · linarith only [h242, h679, hlam]
                                              · linarith only [h678, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h350, h660, h662, h668, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p670_1]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h347, h349, h350, h662, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p670_1, u2ehi3]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p670_1, u5ehi1]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            rcases p670_3 (m.d 0 1) (by simp) with h687 | h687
                                            · linarith only [h687, hlam, p670_0]
                                            · rcases p670_3 (m.d 1 2) (by simp) with h689 | h689
                                              · rcases p670_3 (m.d 1 3) (by simp) with h690 | h690
                                                · rcases p670_3 (m.d 1 4) (by simp) with h691 | h691
                                                  · linarith only [h660, h691, hlam]
                                                  · linarith only [h308, h691, hlam]
                                                · linarith only [h690, hlam, p670_0]
                                              · linarith only [h0, h689, hlam]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h657, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h347, h349, h350, h662, h668, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p670_1, u2ehi3]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h347, h349, h350, h657, h662, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p670_1, u2ehi3]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            rcases p670_3 (m.d 0 1) (by simp) with h700 | h700
                                            · linarith only [h700, hlam, p670_0]
                                            · rcases p670_3 (m.d 1 2) (by simp) with h702 | h702
                                              · rcases p670_3 (m.d 1 3) (by simp) with h703 | h703
                                                · rcases p670_3 (m.d 1 4) (by simp) with h704 | h704
                                                  · rcases p670_3 (m.d 1 5) (by simp) with h705 | h705
                                                    · linarith only [h662, h705, hlam]
                                                    · linarith only [h344, h705, hlam]
                                                  · linarith only [h704, hlam, p670_0]
                                                · linarith only [h242, h703, hlam]
                                              · linarith only [h0, h702, hlam]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h658, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h660, hlam, p670_1]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h347, h349, h350, h662, h668, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p670_1, u2ehi3]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            rcases p670_3 (m.d 0 1) (by simp) with h715 | h715
                                            · linarith only [h715, hlam, p670_0]
                                            · rcases p670_3 (m.d 1 2) (by simp) with h717 | h717
                                              · rcases p670_3 (m.d 1 3) (by simp) with h718 | h718
                                                · rcases p670_3 (m.d 1 4) (by simp) with h719 | h719
                                                  · rcases p670_3 (m.d 1 5) (by simp) with h720 | h720
                                                    · rcases h4bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h308, hlam, p721_1]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h349, h350, hc35, hlam, hphi, ht23, p721_1, u2ehi3]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h349, h350, h668, hc34, hc45, hlam, hphi, p721_1]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h655, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        rcases p721_3 (m.d 0 4) (by simp) with h727 | h727
                                                        · linarith only [h308, h727, hlam]
                                                        · rcases p721_3 (m.d 1 4) (by simp) with h729 | h729
                                                          · rcases p721_3 (m.d 2 4) (by simp) with h730 | h730
                                                            · linarith only [h658, h730, hlam]
                                                            · rcases p721_3 (m.d 3 4) (by simp) with h732 | h732
                                                              · linarith only [h660, h732, hlam]
                                                              · rcases p721_3 (m.d 4 5) (by simp) with h734 | h734
                                                                · linarith only [h662, h734, hlam]
                                                                · linarith only [h655, h734, hlam]
                                                          · linarith only [h308, h729, hlam]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        rcases p721_3 (m.d 0 4) (by simp) with h739 | h739
                                                        · linarith only [h308, h739, hlam]
                                                        · linarith only [h347, h739, hlam]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h349, h350, h662, h668, hlam, p721_2]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h657, h660, h668, hc12, hlam, hphi, ht01, ht0b, ht5b, p721_1, u5ehi3]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h347, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h658, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h346, h350, h663, h668, hc34, hc45, hlam, hphi, p721_1]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h666, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h349, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h660, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h663, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h668, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h347, hc45, hlam, hphi, ht23, ht34, p721_1, u2ehi3]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h662, hlam, p721_0]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [h657, h660, h662, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p721_1, u2ehi3]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        rcases p721_3 (m.d 0 4) (by simp) with h757 | h757
                                                        · linarith only [h655, h757, hlam]
                                                        · linarith only [h349, h757, hlam]
                                                      · have p721_0 := h721c.1
                                                        have p721_1 := h721c.2.1
                                                        have p721_2 := h721c.2.2.1
                                                        have p721_3 := h721c.2.2.2
                                                        linarith only [hlam, p721_0]
                                                    · linarith only [h720, hlam, p670_0]
                                                  · linarith only [h308, h719, hlam]
                                                · linarith only [h242, h718, hlam]
                                              · linarith only [h0, h717, hlam]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h659, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h661, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [h662, hlam, p670_0]
                                          · have p670_0 := h670c.1
                                            have p670_1 := h670c.2.1
                                            have p670_2 := h670c.2.2.1
                                            have p670_3 := h670c.2.2.2
                                            linarith only [hlam, p670_0]
                                  · linarith only [h349, h350, h663, hc23, hc35, hlam, hphi]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                                    · linarith only [h346, h771, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h773 | h773
                                      · linarith only [h0, h347, h773, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h775 | h775
                                        · linarith only [h346, h350, h657, h661, h662, h770, h775, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                        · rcases h1bigk with h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h0, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h242, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h308, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h344, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            rcases p777_3 (m.d 0 1) (by simp) with h783 | h783
                                            · linarith only [h783, hlam, p777_0]
                                            · rcases p777_3 (m.d 1 2) (by simp) with h785 | h785
                                              · rcases p777_3 (m.d 1 3) (by simp) with h786 | h786
                                                · linarith only [h657, h786, hlam]
                                                · linarith only [h242, h786, hlam]
                                              · linarith only [h785, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h350, h661, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h308, hc01, hc12, hlam, hphi, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p777_1, u5ehi1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            rcases p777_3 (m.d 0 1) (by simp) with h794 | h794
                                            · linarith only [h794, hlam, p777_0]
                                            · rcases p777_3 (m.d 1 2) (by simp) with h796 | h796
                                              · rcases p777_3 (m.d 1 3) (by simp) with h797 | h797
                                                · rcases p777_3 (m.d 1 4) (by simp) with h798 | h798
                                                  · linarith only [h660, h798, hlam]
                                                  · linarith only [h308, h798, hlam]
                                                · linarith only [h797, hlam, p777_0]
                                              · linarith only [h0, h796, hlam]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h657, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h308, hc01, hc13, hlam, hphi, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h347, h349, h350, h657, h661, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p777_1, u2ehi3]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h662, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h658, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h660, hlam, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h662, hlam, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            rcases p777_3 (m.d 0 1) (by simp) with h812 | h812
                                            · linarith only [h812, hlam, p777_0]
                                            · rcases p777_3 (m.d 1 2) (by simp) with h814 | h814
                                              · rcases p777_3 (m.d 1 3) (by simp) with h815 | h815
                                                · rcases p777_3 (m.d 1 4) (by simp) with h816 | h816
                                                  · linarith only [h662, h816, hlam]
                                                  · linarith only [h308, h816, hlam]
                                                · linarith only [h242, h815, hlam]
                                              · linarith only [h0, h814, hlam]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h659, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h661, hlam, p777_0]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [h308, hc01, hc15, hlam, hphi, p777_1]
                                          · have p777_0 := h777c.1
                                            have p777_1 := h777c.2.1
                                            have p777_2 := h777c.2.2.1
                                            have p777_3 := h777c.2.2.2
                                            linarith only [hlam, p777_0]
                                  · linarith only [h349, h350, h657, h661, h770, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
                                · linarith only [h347, h655, h660, h661, h826, hc35, hlam, hphi, ht23, u2ehi3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h828 | h828
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h829 | h829
                                    · linarith only [h242, h661, h829, hc01, hc23, hlam, hphi, ht12]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h831 | h831
                                      · linarith only [h0, h344, h347, h348, h826, h831, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h833 | h833
                                        · linarith only [h242, h308, h346, h661, h826, h828, h833, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                        · rcases h1bigk with h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h0, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h242, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h308, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h344, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            rcases p835_3 (m.d 0 1) (by simp) with h841 | h841
                                            · linarith only [h841, hlam, p835_0]
                                            · rcases p835_3 (m.d 1 2) (by simp) with h843 | h843
                                              · rcases p835_3 (m.d 1 3) (by simp) with h844 | h844
                                                · linarith only [h657, h844, hlam]
                                                · linarith only [h242, h844, hlam]
                                              · linarith only [h843, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h242, hc01, hc12, hlam, hphi, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h308, hc01, hc12, hlam, hphi, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h344, h348, hc12, hlam, hphi, ht01, ht0b, ht5b, p835_1, u5ehi2]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h661, hc01, hc35, hlam, hphi, ht12, ht23, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h657, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h308, h347, h661, h833, hc45, hlam, hphi, ht23, ht34, p835_1, u2ehi3]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h661, hlam, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h660, h661, h833, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h658, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h660, hlam, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h826, hlam, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            rcases p835_3 (m.d 0 1) (by simp) with h862 | h862
                                            · linarith only [h862, hlam, p835_0]
                                            · rcases p835_3 (m.d 1 2) (by simp) with h864 | h864
                                              · rcases p835_3 (m.d 1 3) (by simp) with h865 | h865
                                                · linarith only [h661, h865, hlam]
                                                · linarith only [h242, h865, hlam]
                                              · linarith only [h0, h864, hlam]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h659, hlam, p835_0]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h242, hc01, hc15, hlam, hphi, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [h308, hc01, hc15, hlam, hphi, p835_1]
                                          · have p835_0 := h835c.1
                                            have p835_1 := h835c.2.1
                                            have p835_2 := h835c.2.2.1
                                            have p835_3 := h835c.2.2.2
                                            linarith only [hlam, p835_0]
                                  · linarith only [h349, h350, h828, hc35, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h242, h349, h660, hlam]
                          · linarith only [h0, h346, h659, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h347, h348, h658, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h348, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h878 | h878
                  · linarith only [h349, h878, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h880 | h880
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h881 | h881
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h882 | h882
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h883 | h883
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h884 | h884
                            · linarith only [h349, h880, h881, h884, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h886 | h886
                              · linarith only [h346, h878, h884, h886, hc34, hlam, hphi, ht23, u2ehi2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h888 | h888
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                                  · linarith only [h242, h884, h889, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                                    · linarith only [h344, h346, h348, h886, h891, hc02, hlam, hphi, ht0b, ht5b, u5ehi2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                                      · linarith only [h0, h347, h893, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                      · linarith only [h349, h880, h893, hc34, hlam, hphi, ht23, u2ehi3]
                                · linarith only [h308, h880, h888, hlam]
                          · linarith only [h0, h346, h883, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h346, h882, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h346, h881, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h900 | h900
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h901 | h901
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h904 | h904
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h905 | h905
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h906 | h906
                                  · linarith only [h346, h349, h906, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h908 | h908
                                    · linarith only [h346, h878, h908, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h910 | h910
                                      · linarith only [h347, h880, h910, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h912 | h912
                                        · linarith only [h346, h349, h880, h912, hc34, hlam, hphi, ht23, u2ehi2]
                                        · linarith only [h346, h349, h900, h903, h905, h912, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h346, h349, h903, h905, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h346, h349, h903, h904, hc35, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h917 | h917
                              · linarith only [h903, h917, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h919 | h919
                                · linarith only [h346, h349, h880, h903, h919, hc34, hlam, hphi, ht23, u2ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h921 | h921
                                  · linarith only [h346, h349, h921, hlam]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                                    · linarith only [h242, h346, h903, h923, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h925 | h925
                                      · linarith only [h347, h919, h925, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h927 | h927
                                        · linarith only [h308, h347, h919, h927, hc34, hlam, hphi, ht23, u2ehi3]
                                        · linarith only [h346, h349, h927, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h346, h902, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h347, h348, h901, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h346, h348, h900, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h346, h348, hc25, hlam, hphi, u2ehi2]
            · linarith only [h346, h347, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h935 | h935
            · linarith only [h346, h935, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h937 | h937
              · linarith only [h346, h937, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h939 | h939
                · rcases m.htr 0 3 5 (by decide) (by decide) with h940 | h940
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h941 | h941
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h942 | h942
                      · linarith only [h346, h939, h941, h942, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h944 | h944
                        · linarith only [h935, h941, h942, h944, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
                          · linarith only [h937, h942, h946, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h949 | h949
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h951 | h951
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h952 | h952
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h953 | h953
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h954 | h954
                                        · linarith only [h939, h954, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                        · rcases h1bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h0, hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h242, hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h308, hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h344, hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h946, h951, h953, hc01, hc23, hlam, hphi, ht12, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h942, hlam, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h944, hlam, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h946, hlam, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            rcases p956_3 (m.d 0 1) (by simp) with h967 | h967
                                            · linarith only [h967, hlam, p956_0]
                                            · rcases p956_3 (m.d 1 2) (by simp) with h969 | h969
                                              · linarith only [h942, h969, hlam]
                                              · linarith only [h0, h969, hlam]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h942, hc23, hlam, hphi, p956_1, u2ehi1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h942, h950, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p956_1, u5ehi1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h344, h941, h942, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p956_1, u5ehi3]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            rcases p956_3 (m.d 0 1) (by simp) with h976 | h976
                                            · linarith only [h976, hlam, p956_0]
                                            · rcases p956_3 (m.d 1 2) (by simp) with h978 | h978
                                              · linarith only [h944, h978, hlam]
                                              · linarith only [h0, h978, hlam]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h0, hc01, hc14, hlam, hphi, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h948, hlam, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h344, h941, h944, h951, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p956_1, u5ehi3]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            rcases p956_3 (m.d 0 1) (by simp) with h985 | h985
                                            · linarith only [h985, hlam, p956_0]
                                            · rcases p956_3 (m.d 1 2) (by simp) with h987 | h987
                                              · linarith only [h946, h987, hlam]
                                              · linarith only [h0, h987, hlam]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h0, hc01, hc15, hlam, hphi, p956_1]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h949, hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [h950, hlam, p956_0]
                                          · have p956_0 := h956c.1
                                            have p956_1 := h956c.2.1
                                            have p956_2 := h956c.2.2.1
                                            have p956_3 := h956c.2.2.2
                                            linarith only [hlam, p956_0]
                                      · linarith only [h941, h944, h950, h953, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                                    · linarith only [h308, h940, h941, h944, h951, h952, hc05, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h242, h939, h941, h942, h951, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · linarith only [h308, h941, h950, hlam]
                              · linarith only [h242, h940, h949, hlam]
                            · linarith only [h242, h939, h948, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1000 | h1000
                      · linarith only [h1000, h346, h940, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
                        · linarith only [h1000, h1002, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1004 | h1004
                          · linarith only [h1000, h1004, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1006 | h1006
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1007 | h1007
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1008 | h1008
                                · linarith only [h1002, h1008, h935, h941, hc24, hlam, hphi, u2ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1010 | h1010
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1011 | h1011
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1012 | h1012
                                      · linarith only [h1010, h1012, h935, h941, hc23, hlam, hphi, u2ehi0]
                                      · linarith only [h1012, h935, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                    · linarith only [h1000, h1011, h242, h940, hlam]
                                  · linarith only [h1000, h1010, h242, h940, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · linarith only [h1007, h242, h940, hlam]
                            · linarith only [h1006, h242, h939, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1019 | h1019
                    · linarith only [h1019, h939, h940, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1021 | h1021
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1022 | h1022
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1023 | h1023
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1024 | h1024
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1025 | h1025
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1026 | h1026
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1027 | h1027
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1028 | h1028
                                    · linarith only [h1021, h1028, h935, h939, h940, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                    · linarith only [h1028, h346, hc35, hlam, hphi, ht23, u2ehi0]
                                  · linarith only [h1027, h346, h939, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · linarith only [h1022, h1026, h935, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1021, h1025, h346, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1021, h1024, h346, h939, h940, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1021, h1023, h346, hc25, hlam, hphi, u2ehi0]
                        · linarith only [h1021, h1022, h346, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1037 | h1037
                        · linarith only [h1021, h1037, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1039 | h1039
                          · linarith only [h1021, h1039, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1042 | h1042
                              · linarith only [h1021, h1042, h346, h940, hc23, hlam, hphi, u2ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1044 | h1044
                                · linarith only [h1041, h1042, h1044, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1046 | h1046
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1047 | h1047
                                    · linarith only [h1037, h1041, h1042, h1047, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h1047, h346, hc35, hlam, hphi, ht23, u2ehi0]
                                  · linarith only [h0, h1021, h1046, h939, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · linarith only [h1041, h242, h939, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1052 | h1052
                  · linarith only [h1052, h939, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1054 | h1054
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1055 | h1055
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1056 | h1056
                        · linarith only [h1054, h1056, h935, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h1055, h1056, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1059 | h1059
                        · linarith only [h1055, h1059, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1061 | h1061
                          · linarith only [h1055, h1061, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1063 | h1063
                            · linarith only [h1054, h1063, h939, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1065 | h1065
                              · linarith only [h1052, h1063, h1065, h346, hc34, hlam, hphi, ht23, u2ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1067 | h1067
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1068 | h1068
                                  · linarith only [h1063, h1068, h242, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h1068, h346, hc34, hlam, hphi, ht23, u2ehi0]
                                · linarith only [h1054, h1067, h308, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1072 | h1072
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1073 | h1073
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1074 | h1074
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1075 | h1075
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1076 | h1076
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1077 | h1077
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1078 | h1078
                                  · linarith only [h1072, h1078, h346, h939, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1078, h346, hc34, hlam, hphi, ht23, u2ehi0]
                                · linarith only [h1073, h1077, h935, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1072, h1076, h346, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1072, h1075, h346, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1072, h1074, h346, hc25, hlam, hphi, u2ehi0]
                        · linarith only [h1072, h1073, h346, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1086 | h1086
                        · linarith only [h1072, h1086, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1088 | h1088
                          · linarith only [h1072, h1088, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
                            · linarith only [h1072, h1090, h346, h939, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1092 | h1092
                              · linarith only [h1090, h1092, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1094 | h1094
                                · linarith only [h1054, h1086, h1094, h346, h939, hc24, hlam, hphi, u2ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1096 | h1096
                                  · linarith only [h1096, h346, h939, hc23, hlam, hphi, u2ehi0]
                                  · linarith only [h1096, h346, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
