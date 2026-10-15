import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_L_L_0_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
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
                      · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h13, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h18, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                      · linarith only [h0, h23, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h23, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h21, h22, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h28, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h28, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h31, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h31, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h35, h4, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h34, h37, h4, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h39, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h39, h4, h6, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h34, h42, h5, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h44, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                      · linarith only [h0, h46, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h46, h6, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
                · linarith only [h4, h5, h50, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h5, h54, hc12, hlam, hphi, u2elo3]
                    · linarith only [h4, h5, h52, h53, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h59, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h5, h59, hc12, hlam, hphi, u2elo3]
                    · linarith only [h49, h5, h58, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h4, h5, h63, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h4, h49, h65, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                      · linarith only [h0, h68, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h5, h68, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h71, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h5, h71, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                      · linarith only [h4, h79, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                        · linarith only [h1, h79, h81, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h74, h81, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                      · linarith only [h4, h84, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                        · linarith only [h1, h84, h86, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h74, h86, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h4, h75, h77, hlam]
                · linarith only [h4, h74, h76, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h74, h75, h93, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h95, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                        · linarith only [h1, h95, h97, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h74, h75, h92, h97, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                    · linarith only [h100, h4, h74, h92, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                      · linarith only [h102, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                        · linarith only [h1, h102, h104, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h104, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4, h74, h91, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                      · linarith only [h112, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                        · linarith only [h1, h108, h112, h114, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h1, h112, h116, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h108, h116, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h108, h111, h74, hlam]
                  · linarith only [h108, h109, h110, h74, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                      · linarith only [h123, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                        · linarith only [h1, h108, h123, h125, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                          · linarith only [h1, h123, h127, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h108, h127, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h108, h109, h122, h4, hlam]
                  · linarith only [h108, h121, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                      · linarith only [h0, h135, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                        · linarith only [h1, h135, h137, h74, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h0, h108, h139, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                            · linarith only [h1, h141, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h132, h141, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                      · linarith only [h0, h144, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                        · linarith only [h0, h146, h74, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h0, h108, h148, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                            · linarith only [h1, h150, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h132, h144, h150, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                    · linarith only [h132, h133, h153, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                      · linarith only [h0, h155, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                        · linarith only [h0, h157, h74, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                          · linarith only [h0, h108, h159, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                            · linarith only [h1, h161, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h132, h133, h155, h161, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h164, h166, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                        · linarith only [h0, h168, h74, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                          · linarith only [h0, h108, h170, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                            · linarith only [h1, h132, h164, h172, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                              · linarith only [h172, h174, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h164, h166, h174, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h132, h164, h165, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                      · linarith only [h0, h179, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                        · linarith only [h1, h179, h181, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                          · linarith only [h1, h108, h179, h183, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                            · linarith only [h1, h185, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                              · linarith only [h164, h185, h187, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                                · linarith only [h189, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h178, h189, h2, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                      · linarith only [h0, h192, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                        · linarith only [h0, h194, h74, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                          · linarith only [h1, h108, h192, h196, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                            · linarith only [h1, h132, h198, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                              · linarith only [h1, h164, h200, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                                · linarith only [h132, h178, h2, h202, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                                  · linarith only [h0, h132, h204, h4, hc12, hlam, hphi, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                                    · linarith only [h0, h164, h204, h206, h4, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                                      · linarith only [h0, h132, h178, h208, h4, hc12, hlam, hphi, u2elo3]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                                        · linarith only [h0, h204, h208, h210, h4, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h0, h204, h210, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
          · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
            · rcases m.htr 0 2 5 (by decide) (by decide) with h215 | h215
              · linarith only [h0, h215, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
                · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
                  · linarith only [h1, h218, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
                    · linarith only [h2, h220, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h222, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h213, h215, h222, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h225 | h225
                  · linarith only [h0, h214, h217, h225, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h227 | h227
                    · linarith only [h0, h214, h227, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
                      · linarith only [h0, h229, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h213, h215, h229, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
              · linarith only [h2, h214, h232, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
                · linarith only [h213, h214, h234, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h2, h213, h214, h236, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                    · linarith only [h2, h238, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                      · linarith only [h0, h240, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h213, h214, h240, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h243 | h243
            · rcases m.htr 0 2 5 (by decide) (by decide) with h244 | h244
              · linarith only [h0, h213, h244, h3, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h246 | h246
                · rcases m.htr 0 3 5 (by decide) (by decide) with h247 | h247
                  · linarith only [h1, h247, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                    · linarith only [h1, h213, h243, h249, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                      · linarith only [h0, h251, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                        · linarith only [h1, h251, h253, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h243, h244, h253, hc12, hlam, hphi, u2elo4]
                · linarith only [h213, h243, h246, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h257 | h257
              · linarith only [h1, h213, h257, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
                · rcases m.htr 0 3 5 (by decide) (by decide) with h260 | h260
                  · linarith only [h1, h260, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                    · linarith only [h1, h259, h262, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                      · linarith only [h213, h264, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                        · linarith only [h0, h243, h266, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                          · linarith only [h0, h1, h257, h268, h3, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1, h264, h268, h3, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h271 | h271
                  · linarith only [h2, h259, h271, h3, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
                    · linarith only [h2, h273, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                      · linarith only [h213, h275, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                        · linarith only [h0, h277, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                          · linarith only [h1, h275, h279, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h1, h275, h279, h3, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h282 | h282
        · rcases m.htr 0 2 3 (by decide) (by decide) with h283 | h283
          · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
            · linarith only [h0, h2, h284, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
              · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
                · linarith only [h0, h2, h283, h287, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                      · linarith only [h0, h2, h291, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h283, h284, h291, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h283, h289, h290, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h2, h296, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h283, h284, h296, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h286, h295, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h300 | h300
                · linarith only [h1, h2, h300, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h302 | h302
                  · linarith only [h283, h286, h302, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                      · linarith only [h0, h2, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h283, h284, h305, hc12, hlam, hphi, u2elo3]
                    · linarith only [h2, h282, h304, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
            · linarith only [h0, h2, h283, h309, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h311 | h311
              · rcases m.htr 0 3 4 (by decide) (by decide) with h312 | h312
                · linarith only [h1, h2, h312, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                      · linarith only [h0, h316, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                        · linarith only [h1, h2, h309, h316, h318, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h2, h316, h318, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h283, h311, h315, hc12, hlam, hphi, u2elo2]
                  · linarith only [h283, h311, h314, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h323 | h323
                · linarith only [h1, h2, h323, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h325 | h325
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                      · linarith only [h0, h327, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
                        · linarith only [h1, h2, h327, h329, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h1, h2, h327, h329, hc12, hlam, hphi, u2elo3]
                    · linarith only [h1, h2, h325, h326, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h333 | h333
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
                      · linarith only [h283, h334, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h336 | h336
                        · linarith only [h0, h2, h336, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h1, h2, h334, h336, hc12, hlam, hphi, u2elo3]
                    · linarith only [h2, h282, h333, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h340 | h340
          · rcases m.htr 0 2 4 (by decide) (by decide) with h341 | h341
            · linarith only [h0, h2, h341, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h343 | h343
              · linarith only [h0, h282, h343, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h345 | h345
                · linarith only [h0, h2, h340, h345, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
                  · linarith only [h0, h282, h340, h347, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h349 | h349
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
                      · linarith only [h0, h350, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h340, h341, h350, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                      · linarith only [h0, h2, h349, h353, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h340, h341, h353, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
            · linarith only [h1, h2, h340, h356, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h358 | h358
              · linarith only [h1, h282, h340, h358, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h360 | h360
                · linarith only [h1, h2, h360, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h362 | h362
                  · linarith only [h1, h282, h362, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h364 | h364
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
                      · linarith only [h0, h282, h340, h364, h365, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
                        · linarith only [h0, h356, h364, h367, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1, h2, h365, h367, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                      · linarith only [h340, h370, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                        · linarith only [h0, h372, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h2, h370, h372, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h375 | h375
      · rcases m.htr 0 1 5 (by decide) (by decide) with h376 | h376
        · rcases m.htr 0 2 3 (by decide) (by decide) with h377 | h377
          · linarith only [h0, h1, h377, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h379 | h379
            · rcases m.htr 0 2 5 (by decide) (by decide) with h380 | h380
              · rcases m.htr 0 3 4 (by decide) (by decide) with h381 | h381
                · rcases m.htr 0 3 5 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                      · linarith only [h0, h377, h384, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h384, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h387 | h387
                      · linarith only [h0, h387, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h387, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h1, h380, h382, hlam]
                · linarith only [h0, h1, h379, h381, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
                · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                    · linarith only [h379, h380, h394, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                      · linarith only [h0, h396, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h396, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1, h376, h393, hlam]
                · linarith only [h0, h1, h379, h380, h392, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h401 | h401
              · rcases m.htr 0 3 4 (by decide) (by decide) with h402 | h402
                · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                      · linarith only [h0, h1, h405, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h405, hc12, hlam, hphi, u2elo2]
                    · linarith only [h379, h401, h404, hlam]
                  · linarith only [h0, h1, h379, h401, h403, hc12, hlam, hphi, u2elo3]
                · linarith only [h1, h375, h402, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h411 | h411
                · rcases m.htr 0 3 5 (by decide) (by decide) with h412 | h412
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h413 | h413
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
                      · linarith only [h377, h414, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h414, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                      · linarith only [h0, h417, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h417, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1, h376, h412, hlam]
                · linarith only [h1, h375, h411, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h422 | h422
          · linarith only [h0, h1, h422, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h424 | h424
            · rcases m.htr 0 2 5 (by decide) (by decide) with h425 | h425
              · linarith only [h0, h376, h422, h425, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h427 | h427
                · rcases m.htr 0 3 5 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
                    · linarith only [h0, h376, h422, h424, h429, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
                      · linarith only [h0, h422, h431, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h431, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h434 | h434
                    · linarith only [h0, h1, h424, h425, h428, h434, hc12, hlam, hphi, u2elo4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h436 | h436
                      · linarith only [h0, h1, h428, h436, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1, h436, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h424, h425, h427, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h440 | h440
              · linarith only [h375, h376, h424, h440, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h442 | h442
                · rcases m.htr 0 3 5 (by decide) (by decide) with h443 | h443
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
                    · linarith only [h375, h376, h444, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                      · linarith only [h0, h376, h443, h446, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h446, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
                    · linarith only [h1, h375, h443, h449, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
                      · linarith only [h0, h1, h443, h451, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1, h451, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h375, h442, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h455 | h455
        · rcases m.htr 0 2 3 (by decide) (by decide) with h456 | h456
          · linarith only [h0, h1, h456, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h458 | h458
            · linarith only [h0, h375, h458, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h460 | h460
              · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
                · rcases m.htr 0 3 5 (by decide) (by decide) with h462 | h462
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h464 | h464
                      · linarith only [h0, h456, h464, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h464, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h375, h458, h460, h463, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h375, h458, h460, h461, h462, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                      · linarith only [h0, h471, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h471, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h1, h458, h460, h461, h470, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h1, h458, h460, h469, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 3 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                      · linarith only [h0, h479, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h479, hc12, hlam, hphi, u2elo2]
                    · linarith only [h375, h455, h478, hlam]
                  · linarith only [h375, h455, h476, h477, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
                      · linarith only [h0, h486, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h486, hc12, hlam, hphi, u2elo2]
                    · linarith only [h1, h455, h476, h485, hlam]
                  · linarith only [h1, h455, h484, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h491 | h491
          · linarith only [h0, h1, h491, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h493 | h493
            · linarith only [h0, h375, h493, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h495 | h495
              · linarith only [h0, h455, h495, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h497 | h497
                · rcases m.htr 0 3 5 (by decide) (by decide) with h498 | h498
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
                      · linarith only [h0, h455, h491, h497, h499, h500, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h500, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                      · linarith only [h0, h503, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h503, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h506 | h506
                    · linarith only [h497, h498, h506, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
                      · linarith only [h0, h375, h497, h498, h508, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h0, h1, h508, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                      · linarith only [h0, h513, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h513, hc12, hlam, hphi, u2elo2]
                    · linarith only [h497, h511, h512, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h517 | h517
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
                      · linarith only [h0, h518, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h518, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h521 | h521
                      · linarith only [h0, h521, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h521, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h524 | h524
    · rcases m.htr 0 1 4 (by decide) (by decide) with h525 | h525
      · rcases m.htr 0 1 5 (by decide) (by decide) with h526 | h526
        · rcases m.htr 0 2 3 (by decide) (by decide) with h527 | h527
          · rcases m.htr 0 2 4 (by decide) (by decide) with h528 | h528
            · rcases m.htr 0 2 5 (by decide) (by decide) with h529 | h529
              · rcases m.htr 0 3 4 (by decide) (by decide) with h530 | h530
                · rcases m.htr 0 3 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h535 | h535
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                            · linarith only [h524, h536, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h524, h530, h533, h536, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h535, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h534, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h533, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h542 | h542
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h543 | h543
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h544 | h544
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h545 | h545
                            · linarith only [h0, h524, h545, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h0, h524, h530, h545, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h544, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h543, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h542, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h551 | h551
                    · linarith only [h530, h531, h551, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h554 | h554
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h555 | h555
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h556 | h556
                            · linarith only [h524, h556, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h526, h530, h531, h553, h556, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h555, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h554, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h553, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h562 | h562
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h563 | h563
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h567 | h567
                            · linarith only [h524, h530, h567, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                              · linarith only [h0, h525, h567, h569, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h562, h569, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h566, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h524, h564, h565, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h564, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h530, h562, h563, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h580 | h580
                            · linarith only [h0, h524, h530, h580, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                              · linarith only [h0, h524, h562, h582, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
                                · linarith only [h0, h525, h584, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · linarith only [h0, h525, h576, h580, h584, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h579, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h524, h577, h578, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h577, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h591 | h591
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h593 | h593
                            · linarith only [h524, h530, h593, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
                              · linarith only [h0, h524, h562, h576, h595, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                                · linarith only [h525, h576, h597, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h599 | h599
                                  · linarith only [h525, h530, h590, h593, h599, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                                    · linarith only [h524, h562, h576, h590, h601, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
                                      · linarith only [h0, h524, h525, h530, h576, h590, h591, h603, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h605 | h605
                                        · rcases h3bigk with h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h590, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p606_1, u0elo2]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h0, h524, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p606_1, u2elo1]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h530, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h562, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h524, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h0, h524, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p606_1, u2elo1]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h593, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h595, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h527, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h590, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h599, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h601, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            rcases p606_3 (m.d 0 3) (by simp) with h622 | h622
                                            · linarith only [h622, hlam, p606_0]
                                            · rcases p606_3 (m.d 1 3) (by simp) with h624 | h624
                                              · linarith only [h593, h624, hlam]
                                              · rcases p606_3 (m.d 2 3) (by simp) with h626 | h626
                                                · linarith only [h599, h626, hlam]
                                                · rcases p606_3 (m.d 3 4) (by simp) with h628 | h628
                                                  · rcases p606_3 (m.d 3 5) (by simp) with h629 | h629
                                                    · linarith only [h605, h629, hlam]
                                                    · linarith only [h562, h629, hlam]
                                                  · linarith only [h628, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            rcases p606_3 (m.d 0 3) (by simp) with h633 | h633
                                            · linarith only [h530, h633, hlam]
                                            · linarith only [h524, h633, hlam]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            rcases p606_3 (m.d 0 3) (by simp) with h636 | h636
                                            · linarith only [h530, h636, hlam]
                                            · linarith only [h527, h636, hlam]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h530, h576, h605, hc03, hc34, hlam, hphi, p606_1]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            rcases p606_3 (m.d 0 3) (by simp) with h641 | h641
                                            · linarith only [h641, hlam, p606_0]
                                            · rcases p606_3 (m.d 1 3) (by simp) with h643 | h643
                                              · linarith only [h595, h643, hlam]
                                              · rcases p606_3 (m.d 2 3) (by simp) with h645 | h645
                                                · linarith only [h601, h645, hlam]
                                                · rcases p606_3 (m.d 3 4) (by simp) with h647 | h647
                                                  · rcases p606_3 (m.d 3 5) (by simp) with h648 | h648
                                                    · rcases h5bigk with h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [hlam, p649_0]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h597, hc14, hlam, hphi, ht0b, ht45, ht5b, p649_1, u0elo4]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h0, h526, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p649_1, u2elo1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h562, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h576, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h526, hlam, p649_0]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [hlam, p649_0]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h0, h526, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p649_1, u2elo1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h595, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h597, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h529, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h592, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [hlam, p649_0]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h601, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h603, hlam, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        rcases p649_3 (m.d 0 5) (by simp) with h665 | h665
                                                        · linarith only [h562, h665, hlam]
                                                        · rcases p649_3 (m.d 1 5) (by simp) with h667 | h667
                                                          · linarith only [h595, h667, hlam]
                                                          · rcases p649_3 (m.d 2 5) (by simp) with h669 | h669
                                                            · linarith only [h601, h669, hlam]
                                                            · rcases p649_3 (m.d 3 5) (by simp) with h671 | h671
                                                              · rcases p649_3 (m.d 4 5) (by simp) with h672 | h672
                                                                · linarith only [h605, h672, hlam]
                                                                · linarith only [h576, h672, hlam]
                                                              · linarith only [h562, h671, hlam]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        rcases p649_3 (m.d 0 5) (by simp) with h676 | h676
                                                        · linarith only [h562, h676, hlam]
                                                        · linarith only [h526, h676, hlam]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        rcases p649_3 (m.d 0 5) (by simp) with h679 | h679
                                                        · linarith only [h562, h679, hlam]
                                                        · linarith only [h529, h679, hlam]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [hlam, p649_0]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h524, h530, h576, h590, h605, hc23, hc34, hlam, hphi, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h526, h590, h593, h597, h605, hc23, hc34, hlam, hphi, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h590, h593, h597, h605, hc23, hc34, hlam, hphi, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h599, h603, h605, hc23, hc34, hlam, hphi, p649_1]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [h605, hlam, p649_0]
                                                      · have p649_0 := h649c.1
                                                        have p649_1 := h649c.2.1
                                                        have p649_2 := h649c.2.2.1
                                                        have p649_3 := h649c.2.2.2
                                                        linarith only [hlam, p649_0]
                                                    · linarith only [h648, hlam, p606_0]
                                                  · linarith only [h530, h647, hlam]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            rcases p606_3 (m.d 0 3) (by simp) with h691 | h691
                                            · linarith only [h562, h691, hlam]
                                            · linarith only [h524, h691, hlam]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            rcases p606_3 (m.d 0 3) (by simp) with h694 | h694
                                            · linarith only [h562, h694, hlam]
                                            · linarith only [h527, h694, hlam]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [h605, hlam, p606_0]
                                          · have p606_0 := h606c.1
                                            have p606_1 := h606c.2.1
                                            have p606_2 := h606c.2.2.1
                                            have p606_3 := h606c.2.2.2
                                            linarith only [hlam, p606_0]
                                        · rcases h3bigk with h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h590, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p699_1, u0elo2]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h0, h524, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p699_1, u2elo1]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h530, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h562, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h524, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h526, h593, h597, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p699_1, u0elo4]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h593, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h595, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h527, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h590, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h599, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h601, hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h605, hc03, hc45, hlam, hphi, ht34, p699_1]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h605, hc13, hc45, hlam, hphi, ht34, p699_1]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h605, hc23, hc45, hlam, hphi, ht34, p699_1]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [hlam, p699_0]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h605, hlam, p699_1]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            rcases p699_3 (m.d 0 3) (by simp) with h720 | h720
                                            · linarith only [h720, hlam, p699_0]
                                            · rcases p699_3 (m.d 1 3) (by simp) with h722 | h722
                                              · linarith only [h595, h722, hlam]
                                              · rcases p699_3 (m.d 2 3) (by simp) with h724 | h724
                                                · linarith only [h601, h724, hlam]
                                                · rcases p699_3 (m.d 3 4) (by simp) with h726 | h726
                                                  · linarith only [h605, h726, hlam]
                                                  · linarith only [h530, h726, hlam]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            rcases p699_3 (m.d 0 3) (by simp) with h729 | h729
                                            · linarith only [h562, h729, hlam]
                                            · linarith only [h524, h729, hlam]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            rcases p699_3 (m.d 0 3) (by simp) with h732 | h732
                                            · linarith only [h562, h732, hlam]
                                            · linarith only [h527, h732, hlam]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [h524, h530, h590, h605, hc23, hc45, hlam, hphi, ht34, p699_1]
                                          · have p699_0 := h699c.1
                                            have p699_1 := h699c.2.1
                                            have p699_2 := h699c.2.2.1
                                            have p699_3 := h699c.2.2.2
                                            linarith only [hlam, p699_0]
                          · linarith only [h0, h592, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h591, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h590, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h0, h526, h529, hlam]
            · linarith only [h0, h525, h528, hlam]
          · linarith only [h0, h524, h527, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h743 | h743
          · rcases m.htr 0 2 4 (by decide) (by decide) with h744 | h744
            · rcases m.htr 0 2 5 (by decide) (by decide) with h745 | h745
              · rcases m.htr 0 3 4 (by decide) (by decide) with h746 | h746
                · rcases m.htr 0 3 5 (by decide) (by decide) with h747 | h747
                  · linarith only [h524, h526, h747, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h749 | h749
                    · linarith only [h524, h526, h746, h749, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h754 | h754
                            · linarith only [h524, h754, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h524, h526, h746, h751, h753, h754, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h745, h753, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h524, h751, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h751, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h760 | h760
                  · linarith only [h525, h526, h746, h760, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h762 | h762
                    · linarith only [h525, h526, h762, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h765 | h765
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
                            · linarith only [h524, h746, h767, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h769 | h769
                              · linarith only [h524, h526, h760, h766, h769, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h771 | h771
                                · linarith only [h525, h526, h762, h766, h771, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h773 | h773
                                  · linarith only [h743, h746, h773, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h775 | h775
                                    · linarith only [h524, h526, h764, h769, h775, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h777 | h777
                                      · linarith only [h525, h526, h765, h771, h777, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h779 | h779
                                        · linarith only [h525, h526, h765, h771, h773, h779, hc23, hc34, hlam, hphi]
                                        · rcases h3bigk with h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p781_1, u0elo2]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h746, h779, hc23, hc45, hlam, hphi, ht34, p781_1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h746, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h760, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h524, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h524, h526, h766, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p781_1, u2elo1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h767, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h769, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h743, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h764, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h773, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h775, hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h779, hc03, hc45, hlam, hphi, ht34, p781_1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h764, h779, hc23, hc45, hlam, hphi, ht34, p781_1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h779, hc23, hc45, hlam, hphi, ht34, p781_1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [hlam, p781_0]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h779, hlam, p781_1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            rcases p781_3 (m.d 0 3) (by simp) with h802 | h802
                                            · linarith only [h802, hlam, p781_0]
                                            · rcases p781_3 (m.d 1 3) (by simp) with h804 | h804
                                              · linarith only [h769, h804, hlam]
                                              · rcases p781_3 (m.d 2 3) (by simp) with h806 | h806
                                                · linarith only [h775, h806, hlam]
                                                · rcases p781_3 (m.d 3 4) (by simp) with h808 | h808
                                                  · linarith only [h779, h808, hlam]
                                                  · linarith only [h746, h808, hlam]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            rcases p781_3 (m.d 0 3) (by simp) with h811 | h811
                                            · linarith only [h760, h811, hlam]
                                            · linarith only [h524, h811, hlam]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            rcases p781_3 (m.d 0 3) (by simp) with h814 | h814
                                            · linarith only [h760, h814, hlam]
                                            · linarith only [h743, h814, hlam]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [h524, h746, h764, hc23, hc35, hlam, hphi, p781_1]
                                          · have p781_0 := h781c.1
                                            have p781_1 := h781c.2.1
                                            have p781_2 := h781c.2.2.1
                                            have p781_3 := h781c.2.2.2
                                            linarith only [hlam, p781_0]
                          · linarith only [h745, h766, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h524, h764, h765, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h764, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h822 | h822
                · rcases m.htr 0 3 5 (by decide) (by decide) with h823 | h823
                  · linarith only [h524, h526, h823, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h825 | h825
                    · linarith only [h0, h524, h745, h822, h825, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h827 | h827
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h829 | h829
                          · linarith only [h0, h745, h829, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h524, h827, h829, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h524, h827, h828, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h524, h827, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
                  · linarith only [h0, h525, h745, h822, h834, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                    · linarith only [h0, h525, h745, h836, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h840 | h840
                          · linarith only [h0, h524, h745, h838, h840, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h524, h838, h840, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h524, h838, h839, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h524, h838, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h525, h744, hlam]
          · linarith only [h0, h524, h743, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h847 | h847
        · rcases m.htr 0 2 3 (by decide) (by decide) with h848 | h848
          · rcases m.htr 0 2 4 (by decide) (by decide) with h849 | h849
            · rcases m.htr 0 2 5 (by decide) (by decide) with h850 | h850
              · rcases m.htr 0 3 4 (by decide) (by decide) with h851 | h851
                · linarith only [h524, h525, h851, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h854 | h854
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h855 | h855
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h856 | h856
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h857 | h857
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h858 | h858
                            · linarith only [h524, h851, h858, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
                              · linarith only [h524, h525, h856, h860, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h853, h860, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h525, h856, h857, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h849, h856, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h855, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h525, h847, h854, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h867 | h867
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h868 | h868
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h869 | h869
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h870 | h870
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h871 | h871
                            · linarith only [h524, h851, h871, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h873 | h873
                              · linarith only [h524, h525, h853, h869, h873, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h875 | h875
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h876 | h876
                                  · linarith only [h525, h871, h876, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h878 | h878
                                    · linarith only [h847, h853, h868, h873, h878, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h880 | h880
                                      · linarith only [h849, h880, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h849, h867, h880, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h525, h867, h875, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                          · linarith only [h524, h525, h868, h869, h870, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h524, h868, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h868, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h525, h847, h867, hlam]
              · linarith only [h0, h847, h850, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h889 | h889
              · rcases m.htr 0 3 4 (by decide) (by decide) with h890 | h890
                · linarith only [h0, h524, h849, h890, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h893 | h893
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h894 | h894
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h895 | h895
                        · linarith only [h0, h524, h849, h894, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h524, h894, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h524, h894, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                    · linarith only [h524, h525, h892, h893, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
                        · linarith only [h849, h902, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h524, h901, h902, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h524, h901, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                    · linarith only [h525, h847, h900, hlam]
              · linarith only [h0, h847, h889, hlam]
          · linarith only [h0, h524, h848, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h909 | h909
          · rcases m.htr 0 2 4 (by decide) (by decide) with h910 | h910
            · rcases m.htr 0 2 5 (by decide) (by decide) with h911 | h911
              · rcases m.htr 0 3 4 (by decide) (by decide) with h912 | h912
                · linarith only [h524, h525, h912, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h914 | h914
                  · linarith only [h524, h847, h914, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h916 | h916
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h917 | h917
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h918 | h918
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h919 | h919
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h920 | h920
                            · linarith only [h524, h912, h920, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h922 | h922
                              · linarith only [h524, h847, h914, h922, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h924 | h924
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h925 | h925
                                  · linarith only [h847, h920, h924, h925, hc01, hlam, hphi, ht12, u2elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h927 | h927
                                    · linarith only [h524, h847, h917, h922, h927, hlam]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h929 | h929
                                      · linarith only [h910, h929, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h910, h916, h929, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h910, h916, h924, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h911, h919, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h524, h917, h918, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h917, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h936 | h936
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h937 | h937
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h938 | h938
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h939 | h939
                            · linarith only [h524, h912, h939, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h941 | h941
                              · linarith only [h524, h525, h914, h937, h941, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h943 | h943
                                · linarith only [h524, h525, h916, h936, h937, h943, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · linarith only [h524, h525, h936, h943, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h911, h938, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h524, h910, h936, h937, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h524, h936, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h949 | h949
                · linarith only [h524, h525, h949, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h951 | h951
                  · linarith only [h0, h524, h911, h951, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h953 | h953
                    · linarith only [h910, h911, h953, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h955 | h955
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h957 | h957
                          · linarith only [h525, h910, h911, h957, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h0, h524, h955, h957, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h524, h955, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h955, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h962 | h962
              · rcases m.htr 0 3 4 (by decide) (by decide) with h963 | h963
                · linarith only [h0, h524, h910, h963, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h965 | h965
                  · linarith only [h524, h847, h965, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h967 | h967
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h968 | h968
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h969 | h969
                        · linarith only [h524, h847, h910, h962, h968, h969, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h524, h968, h969, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h968, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h910, h962, h967, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h974 | h974
                · linarith only [h0, h524, h910, h974, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h976 | h976
                  · linarith only [h0, h524, h962, h976, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h979 | h979
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h980 | h980
                        · linarith only [h0, h524, h910, h979, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h524, h979, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h979, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h984 | h984
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h985 | h985
                        · linarith only [h0, h524, h910, h984, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h524, h984, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h524, h984, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h524, h909, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h990 | h990
      · rcases m.htr 0 1 5 (by decide) (by decide) with h991 | h991
        · rcases m.htr 0 2 3 (by decide) (by decide) with h992 | h992
          · rcases m.htr 0 2 4 (by decide) (by decide) with h993 | h993
            · rcases m.htr 0 2 5 (by decide) (by decide) with h994 | h994
              · rcases m.htr 0 3 4 (by decide) (by decide) with h995 | h995
                · rcases m.htr 0 3 5 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h997 | h997
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h998 | h998
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1000 | h1000
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1001 | h1001
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                                · linarith only [h1003, h990, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h1003, h524, h990, h997, h998, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h1002, h524, h992, h996, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1001, h524, h990, h992, h995, h999, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1000, h524, h990, h998, h999, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h524, h998, h999, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h990, h992, h998, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1011 | h1011
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1012 | h1012
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1013 | h1013
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1015 | h1015
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1016 | h1016
                                · linarith only [h1016, h990, h997, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1018 | h1018
                                  · linarith only [h1018, h992, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1018, h992, h995, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h1015, h524, h992, h996, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1012, h1014, h524, h990, h992, h995, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1011, h1012, h1013, h524, h990, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h1011, h1012, h524, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1011, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h524, h991, h996, hlam]
                · linarith only [h524, h990, h995, hlam]
              · linarith only [h0, h991, h994, hlam]
            · linarith only [h524, h990, h992, h993, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1030 | h1030
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1031 | h1031
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1032 | h1032
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1033 | h1033
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1034 | h1034
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1035 | h1035
                      · linarith only [h1035, h992, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1035, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1038 | h1038
                      · linarith only [h0, h1038, h990, h992, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1038, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h0, h1033, h991, h992, hlam]
                · linarith only [h0, h1032, h990, h992, hlam]
              · linarith only [h0, h1031, h991, hlam]
            · linarith only [h0, h1030, h990, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1045 | h1045
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1046 | h1046
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1047 | h1047
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1048 | h1048
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1049 | h1049
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1050 | h1050
                    · linarith only [h1050, h990, h991, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1052 | h1052
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1053 | h1053
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1054 | h1054
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1055 | h1055
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1056 | h1056
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1057 | h1057
                                · linarith only [h1050, h1057, h990, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1059 | h1059
                                  · linarith only [h1045, h1059, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1045, h1048, h1059, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h1045, h1049, h1056, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1045, h1048, h1053, h1055, h524, h990, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1047, h1052, h1053, h1054, h524, h990, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1052, h1053, h524, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1052, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1067 | h1067
                    · linarith only [h1049, h1067, h524, h990, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1069 | h1069
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1070 | h1070
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1071 | h1071
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1072 | h1072
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1073 | h1073
                              · linarith only [h1049, h1069, h1073, h524, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1075 | h1075
                                · linarith only [h1067, h1075, h990, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1077 | h1077
                                  · linarith only [h1045, h1077, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1047, h1048, h1049, h1077, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1048, h1070, h1072, h524, h990, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h1047, h1071, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1069, h1070, h524, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1069, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1048, h524, h990, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1085 | h1085
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1086 | h1086
                  · linarith only [h1045, h1047, h1086, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1088 | h1088
                    · linarith only [h1045, h1047, h1088, h524, h990, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h1045, h1047, h1091, h1092, h524, h990, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h0, h1091, h1092, h990, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h1090, h1091, h524, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                      · linarith only [h0, h1090, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1085, h524, h990, hlam]
            · linarith only [h0, h1046, h990, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1099 | h1099
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1100 | h1100
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1101 | h1101
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1102 | h1102
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1103 | h1103
                    · linarith only [h1103, h990, h991, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1105 | h1105
                      · linarith only [h1045, h1100, h1105, h991, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1105, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1045, h1100, h1102, hlam]
                · linarith only [h1045, h1100, h1101, h990, h991, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1110 | h1110
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1111 | h1111
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1112 | h1112
                    · linarith only [h0, h1100, h1112, h990, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
                      · linarith only [h0, h1045, h1114, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1114, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1117 | h1117
                    · linarith only [h1111, h1117, h524, h990, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1119 | h1119
                      · linarith only [h0, h1045, h1119, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1119, h990, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h0, h1045, h1110, h990, hlam]
            · linarith only [h0, h1099, h990, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1124 | h1124
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1126 | h1126
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1127 | h1127
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1128 | h1128
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1135 | h1135
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1136 | h1136
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1137 | h1137
                                  · linarith only [h1125, h1137, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1128, h1137, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1130, h1136, h990, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h1124, h1125, h1129, h1133, h1134, h1135, h990, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1125, h1128, h1134, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1131, h1133, h524, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1124, h1126, h1131, h1132, h524, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h1124, h1131, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h1124, h1130, h990, hlam]
                  · linarith only [h1124, h1128, h1129, h990, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1148 | h1148
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1149 | h1149
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1150 | h1150
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1151 | h1151
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1152 | h1152
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1153 | h1153
                            · linarith only [h1128, h1148, h1150, h1153, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1155 | h1155
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1156 | h1156
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1157 | h1157
                                  · linarith only [h1125, h1153, h1157, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1159 | h1159
                                    · linarith only [h1126, h1157, h1159, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h1148, h1159, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1124, h1126, h1149, h1152, h1156, h990, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h1124, h1126, h1128, h1148, h1152, h1155, h524, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h0, h1152, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1124, h1126, h1150, h1151, h524, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h1124, h1150, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h1124, h1128, h1149, h524, hlam]
                  · linarith only [h1124, h1148, h524, hlam]
              · linarith only [h0, h1124, h1127, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1170 | h1170
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1171 | h1171
                · linarith only [h1125, h1126, h1171, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1173 | h1173
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1174 | h1174
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1175 | h1175
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1176 | h1176
                        · linarith only [h1125, h1126, h1176, h524, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h1124, h1176, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h0, h1124, h1125, h1175, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h1124, h1174, h990, hlam]
                  · linarith only [h1124, h1173, h524, hlam]
              · linarith only [h0, h1124, h1170, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1183 | h1183
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1184 | h1184
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1185 | h1185
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1186 | h1186
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1187 | h1187
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1188 | h1188
                      · linarith only [h1125, h1183, h1188, h990, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1124, h1188, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h1124, h1187, h990, hlam]
                  · linarith only [h1124, h1125, h1183, h1186, h990, hlam]
                · linarith only [h1125, h1183, h1185, hlam]
              · linarith only [h1124, h1183, h1184, h990, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1195 | h1195
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1196 | h1196
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1197 | h1197
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1198 | h1198
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1199 | h1199
                      · linarith only [h1125, h1199, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1124, h1199, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h0, h1124, h1183, h1198, hlam]
                  · linarith only [h0, h1124, h1183, h1196, h1197, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1205 | h1205
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1206 | h1206
                      · linarith only [h0, h1124, h1125, h1206, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h1124, h1206, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h1124, h1196, h1205, h524, hlam]
                  · linarith only [h0, h1124, h1125, h1204, hlam]
              · linarith only [h0, h1124, h1195, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1212 | h1212
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1213 | h1213
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1214 | h1214
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1216 | h1216
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1217 | h1217
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1218 | h1218
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1219 | h1219
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1220 | h1220
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1221 | h1221
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1222 | h1222
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1223 | h1223
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1224 | h1224
                                  · linarith only [h1212, h1224, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1215, h1224, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1217, h1223, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h1216, h1222, h524, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                            · linarith only [h1215, h1221, h524, hlam]
                          · linarith only [h1214, h1220, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1213, h1219, hlam]
                      · linarith only [h0, h1218, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1233 | h1233
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1234 | h1234
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1235 | h1235
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1236 | h1236
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1237 | h1237
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1238 | h1238
                                · linarith only [h1217, h1233, h1236, h1238, h990, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1240 | h1240
                                  · linarith only [h1212, h1240, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1212, h1215, h1240, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h1212, h1216, h1237, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1215, h1216, h1236, h524, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1214, h1235, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1213, h1234, hlam]
                      · linarith only [h0, h1233, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1248 | h1248
                    · linarith only [h1215, h1216, h1248, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1250 | h1250
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1251 | h1251
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1252 | h1252
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1253 | h1253
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1254 | h1254
                              · linarith only [h1216, h1250, h1254, h524, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1256 | h1256
                                · linarith only [h1248, h1251, h1256, h990, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1258 | h1258
                                  · linarith only [h1212, h1258, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1215, h1258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1214, h1215, h1216, h1253, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1214, h1252, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1213, h1251, hlam]
                      · linarith only [h0, h1250, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1265 | h1265
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1266 | h1266
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1267 | h1267
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1268 | h1268
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1269 | h1269
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1270 | h1270
                            · linarith only [h1215, h1265, h1267, h1270, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1272 | h1272
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1273 | h1273
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1274 | h1274
                                  · linarith only [h1212, h1270, h1274, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1276 | h1276
                                    · linarith only [h1213, h1274, h1276, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h1265, h1276, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1213, h1266, h1273, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h1213, h1215, h1265, h1272, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1214, h1269, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1213, h1268, hlam]
                      · linarith only [h0, h1267, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1215, h1265, h1266, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1285 | h1285
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1286 | h1286
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1287 | h1287
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1288 | h1288
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1289 | h1289
                            · linarith only [h1215, h1286, h1289, h524, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1291 | h1291
                              · linarith only [h1265, h1289, h1291, h524, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1293 | h1293
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                                  · linarith only [h1212, h1294, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1296 | h1296
                                    · linarith only [h1213, h1291, h1294, h1296, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1298 | h1298
                                      · linarith only [h1213, h1298, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h1213, h1285, h1298, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h1213, h1285, h1293, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h0, h1288, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h1287, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1286, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1305 | h1305
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1306 | h1306
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1307 | h1307
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1308 | h1308
                            · linarith only [h1215, h1305, h1308, h524, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1310 | h1310
                              · linarith only [h1265, h1308, h1310, hc03, hc34, hlam, hphi]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1312 | h1312
                                · linarith only [h1285, h1306, h1312, h990, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1314 | h1314
                                  · linarith only [h1212, h1314, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1316 | h1316
                                    · linarith only [h1213, h1310, h1314, h1316, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1318 | h1318
                                      · linarith only [h1213, h1312, h1318, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1320 | h1320
                                        · linarith only [h1308, h1312, h1320, h524, hc01, hc34, hlam, hphi, ht12, ht23]
                                        · linarith only [h1308, h1320, h524, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h1214, h1307, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1306, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1305, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1326 | h1326
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1327 | h1327
                  · linarith only [h1212, h1214, h1327, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1329 | h1329
                    · linarith only [h1212, h1214, h1326, h1329, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1332 | h1332
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1333 | h1333
                          · linarith only [h1214, h1333, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1333, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1213, h1331, h1332, h524, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1212, h1214, h1331, hc01, hlam, hphi, ht12, u2elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1338 | h1338
                  · linarith only [h1213, h1214, h1326, h1338, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1340 | h1340
                    · linarith only [h1213, h1214, h1340, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1342 | h1342
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1343 | h1343
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1344 | h1344
                          · linarith only [h1214, h1344, hc02, hlam, hphi, u2elo1]
                          · linarith only [h0, h1344, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h1342, h1343, h524, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h1212, h1342, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1349 | h1349
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1350 | h1350
                · linarith only [h1212, h1213, h1350, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1352 | h1352
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1353 | h1353
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1354 | h1354
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1355 | h1355
                        · linarith only [h1213, h1355, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1355, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1212, h1354, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1212, h1213, h1352, h1353, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1360 | h1360
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1361 | h1361
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1362 | h1362
                        · linarith only [h1213, h1362, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1362, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1212, h1361, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1213, h1349, h1360, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1367 | h1367
                · linarith only [h1212, h1213, h1367, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1369 | h1369
                  · linarith only [h1212, h1349, h1369, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1371 | h1371
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1373 | h1373
                        · linarith only [h1213, h1373, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1373, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1212, h1372, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1377 | h1377
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1378 | h1378
                        · linarith only [h1213, h1378, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1378, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h1212, h1377, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1382 | h1382
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1383 | h1383
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1384 | h1384
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1385 | h1385
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1386 | h1386
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1387 | h1387
                      · linarith only [h1212, h1387, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1387, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
                      · linarith only [h1212, h1382, h1390, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1390, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1212, h1383, h1385, hlam]
                · linarith only [h1212, h1382, h1384, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1395 | h1395
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1396 | h1396
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1397 | h1397
                    · linarith only [h1382, h1383, h1397, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1399 | h1399
                      · linarith only [h1212, h1382, h1399, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1399, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1402 | h1402
                    · linarith only [h1212, h1382, h1396, h1402, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1404 | h1404
                      · linarith only [h1212, h1382, h1404, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1404, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1212, h1382, h1395, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1408 | h1408
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1410 | h1410
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1411 | h1411
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1412 | h1412
                      · linarith only [h1212, h1412, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1412, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1382, h1408, h1411, hlam]
                  · linarith only [h1382, h1408, h1409, h1410, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1417 | h1417
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1418 | h1418
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1419 | h1419
                      · linarith only [h1212, h1408, h1419, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h1419, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1212, h1408, h1409, h1418, hlam]
                  · linarith only [h1212, h1408, h1417, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1424 | h1424
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1425 | h1425
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1426 | h1426
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1427 | h1427
                      · linarith only [h1212, h1427, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1427, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1430 | h1430
                      · linarith only [h0, h1212, h1430, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1430, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1433 | h1433
                    · linarith only [h1424, h1425, h1433, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1435 | h1435
                      · linarith only [h0, h1212, h1435, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1435, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1438 | h1438
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1439 | h1439
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1440 | h1440
                      · linarith only [h0, h1212, h1440, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1440, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h1424, h1438, h1439, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1444 | h1444
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
                      · linarith only [h0, h1212, h1445, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1445, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1448 | h1448
                      · linarith only [h0, h1212, h1448, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1448, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
