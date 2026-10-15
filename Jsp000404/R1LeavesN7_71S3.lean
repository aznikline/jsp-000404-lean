import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_13_25_L_0_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 2 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h3, h7, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, h3, h5, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h3, h5, h9, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                            · linarith only [h0, h10, h14, h17, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h14, h17, h3, hc23, hc35, hlam, hphi]
                          · linarith only [h10, h16, h9, hc13, hc35, hlam, hphi]
                        · linarith only [h15, h6, h7, hc12, hc25, hlam, hphi]
                      · linarith only [h14, h5, h7, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h6, h7, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h25, h6, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                          · linarith only [h1, h29, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                            · linarith only [h1, h23, h31, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · linarith only [h0, h27, h3, h31, hc23, hc35, hlam, hphi]
                        · linarith only [h0, h27, h28, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h27, h5, h7, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h36 | h36
              · linarith only [h2, h3, h36, h6, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
                · linarith only [h38, h5, h6, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
                  · linarith only [h2, h3, h40, h5, h6, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                    · linarith only [h2, h3, h42, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                        · linarith only [h0, h45, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                          · linarith only [h1, h2, h38, h44, h45, h47, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                            · linarith only [h2, h3, h40, h44, h45, h49, hlam]
                            · linarith only [h2, h3, h44, h45, h49, hc23, hc35, hlam, hphi]
                      · linarith only [h44, h5, h6, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h53 | h53
            · rcases m.htr 0 2 5 (by decide) (by decide) with h54 | h54
              · linarith only [h1, h5, h54, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
                · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h1, h3, h57, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h5, h53, h57, h59, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                      · linarith only [h0, h5, h61, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                            · linarith only [h1, h57, h65, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                              · linarith only [h2, h53, h59, h67, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                              · linarith only [h1, h3, h64, h67, hc34, hc45, hlam, hphi]
                          · linarith only [h1, h56, h61, h63, h64, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h5, h53, h63, hc12, hc23, hlam, hphi]
                · linarith only [h5, h53, h56, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h73 | h73
              · linarith only [h73, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
                · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
                  · linarith only [h1, h3, h76, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h75, h76, h78, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h3, h5, h80, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                        · linarith only [h0, h3, h53, h82, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                            · linarith only [h1, h3, h76, h85, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                              · linarith only [h1, h3, h78, h84, h85, h87, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · linarith only [h1, h3, h84, h87, hc34, hc45, hlam, hphi]
                          · linarith only [h75, h76, h84, hc13, hc35, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h91, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h2, h93, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h5, h95, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                        · linarith only [h0, h3, h53, h97, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                          · linarith only [h1, h75, h99, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
                            · linarith only [h1, h101, h91, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                              · linarith only [h101, h103, h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                                  · linarith only [h0, h101, h106, h3, hc12, hc23, hlam, hphi]
                                  · linarith only [h105, h106, h75, hc03, hc35, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h109 | h109
                                  · linarith only [h105, h109, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                                    · linarith only [h103, h111, h2, h3, h95, h99, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                                      · linarith only [h0, h105, h111, h113, h5, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h105, h113, h5, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h116 | h116
        · linarith only [h116, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h118 | h118
          · rcases m.htr 0 2 4 (by decide) (by decide) with h119 | h119
            · linarith only [h0, h119, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h121 | h121
              · linarith only [h0, h121, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
                · linarith only [h1, h123, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
                  · linarith only [h118, h119, h125, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h127 | h127
                    · linarith only [h127, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                      · linarith only [h0, h127, h129, h2, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h118, h127, h129, h2, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h132 | h132
            · linarith only [h1, h118, h132, h2, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h134 | h134
              · linarith only [h1, h118, h134, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
                · linarith only [h1, h136, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h136, h138, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h140 | h140
                    · linarith only [h140, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
                      · linarith only [h0, h118, h140, h142, h2, hc02, hc45, hlam, hphi, ht23, ht34]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                        · linarith only [h0, h132, h144, h2, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                          · linarith only [h1, h136, h146, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                            · linarith only [h1, h138, h140, h148, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                              · linarith only [h1, h140, h142, h146, h150, h2, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h1, h142, h150, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h153 | h153
      · rcases m.htr 0 1 5 (by decide) (by decide) with h154 | h154
        · linarith only [h154, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h156 | h156
          · linarith only [h0, h1, h156, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h158 | h158
            · rcases m.htr 0 2 5 (by decide) (by decide) with h159 | h159
              · linarith only [h0, h159, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
                · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h162, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h0, h1, h158, h162, h164, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h156, h166, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                            · linarith only [h0, h1, h162, h166, h168, h170, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h168, h170, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h168, h169, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h156, h158, h168, hc12, hc23, hlam, hphi]
                · linarith only [h1, h153, h161, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
              · linarith only [h153, h158, h176, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
                · rcases m.htr 0 3 5 (by decide) (by decide) with h179 | h179
                  · linarith only [h179, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h181 | h181
                    · linarith only [h1, h153, h179, h181, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                      · linarith only [h0, h1, h179, h183, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
                        · linarith only [h0, h1, h158, h179, h185, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                            · linarith only [h0, h1, h179, h183, h188, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h153, h185, h188, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h153, h185, h187, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h153, h178, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h193 | h193
        · linarith only [h193, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h195 | h195
          · linarith only [h0, h1, h195, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
            · linarith only [h0, h153, h197, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h199 | h199
              · linarith only [h0, h199, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h201 | h201
                · rcases m.htr 0 3 5 (by decide) (by decide) with h202 | h202
                  · linarith only [h202, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h204 | h204
                    · linarith only [h201, h202, h204, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
                      · linarith only [h0, h153, h195, h201, h202, h206, hc02, hc35, hlam, hphi, ht23]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                        · linarith only [h0, h153, h197, h208, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h211 | h211
                            · linarith only [h0, h153, h201, h202, h206, h211, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h211, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h201, h210, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h215, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h217 | h217
                    · linarith only [h217, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
                      · linarith only [h0, h1, h201, h217, h219, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                        · linarith only [h0, h1, h201, h217, h221, hc24, hc45, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                          · linarith only [h0, h1, h201, h219, h223, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h223, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h226 | h226
    · rcases m.htr 0 1 4 (by decide) (by decide) with h227 | h227
      · rcases m.htr 0 1 5 (by decide) (by decide) with h228 | h228
        · linarith only [h228, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
          · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
            · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
              · linarith only [h232, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
                · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
                  · linarith only [h0, h226, h232, h235, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h226, h232, h234, h237, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                            · linarith only [h0, h226, h232, h235, h242, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h226, h228, h237, h241, h242, h244, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · linarith only [h226, h228, h241, h244, hc34, hc45, hlam, hphi]
                          · linarith only [h234, h235, h239, h241, hc23, hc35, hlam, hphi]
                        · linarith only [h0, h231, h240, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h230, h239, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
                  · linarith only [h227, h234, h250, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                    · linarith only [h0, h227, h232, h252, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                          · linarith only [h0, h226, h232, h234, h256, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                            · linarith only [h226, h250, h258, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h260 | h260
                              · linarith only [h227, h260, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                                · linarith only [h230, h234, h262, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                                  · linarith only [h226, h227, h228, h254, h258, h264, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h266 | h266
                                    · linarith only [h227, h228, h255, h260, h266, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                                      · linarith only [h0, h227, h232, h256, h266, h268, hc13, hc34, hlam, hphi]
                                      · rcases h3bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h226, h232, h254, h264, hc23, hc35, hlam, hphi, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h226, h232, h264, h268, hc23, hc45, hlam, hphi, ht34, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h234, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h250, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h226, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h0, h226, h232, h264, h268, hc23, hc45, hlam, hphi, ht34, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h256, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h258, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h230, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h254, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h262, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h264, hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h268, hc03, hc45, hlam, hphi, ht34, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h268, hc13, hc45, hlam, hphi, ht34, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h268, hc23, hc45, hlam, hphi, ht34, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h268, hlam, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          rcases p270_3 (m.d 0 3) (by simp) with h291 | h291
                                          · linarith only [h291, hlam, p270_0]
                                          · rcases p270_3 (m.d 1 3) (by simp) with h293 | h293
                                            · linarith only [h258, h293, hlam]
                                            · rcases p270_3 (m.d 2 3) (by simp) with h295 | h295
                                              · linarith only [h264, h295, hlam]
                                              · rcases p270_3 (m.d 3 4) (by simp) with h297 | h297
                                                · linarith only [h268, h297, hlam]
                                                · linarith only [h234, h297, hlam]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          rcases p270_3 (m.d 0 3) (by simp) with h300 | h300
                                          · linarith only [h250, h300, hlam]
                                          · linarith only [h226, h300, hlam]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          rcases p270_3 (m.d 0 3) (by simp) with h303 | h303
                                          · linarith only [h250, h303, hlam]
                                          · linarith only [h230, h303, hlam]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [h226, h234, h254, h268, hc23, hc45, hlam, hphi, ht34, p270_1]
                                        · have p270_0 := h270c.1
                                          have p270_1 := h270c.2.1
                                          have p270_2 := h270c.2.2.1
                                          have p270_3 := h270c.2.2.2
                                          linarith only [hlam, p270_0]
                        · linarith only [h0, h231, h255, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h230, h254, hlam]
            · linarith only [h0, h227, h231, hlam]
          · linarith only [h0, h226, h230, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
        · linarith only [h312, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h314 | h314
          · rcases m.htr 0 2 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 0 2 5 (by decide) (by decide) with h316 | h316
              · linarith only [h316, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h318 | h318
                · linarith only [h226, h227, h318, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
                  · linarith only [h226, h227, h315, h316, h320, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h322 | h322
                    · linarith only [h315, h316, h322, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h326 | h326
                          · linarith only [h226, h227, h318, h322, h326, hc03, hc45, hlam, hphi, ht34]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                            · linarith only [h226, h320, h328, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                              · linarith only [h226, h227, h322, h326, h330, hc13, hc34, hlam, hphi]
                              · linarith only [h226, h227, h324, h330, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h226, h315, h324, h325, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h314, h324, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h335 | h335
              · linarith only [h315, h335, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
                · linarith only [h0, h226, h315, h337, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                  · linarith only [h0, h226, h315, h339, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
                    · linarith only [h341, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                          · linarith only [h0, h226, h315, h337, h344, h345, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
                            · linarith only [h226, h339, h347, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
                              · linarith only [h0, h226, h315, h341, h345, h349, hc13, hc34, hlam, hphi]
                              · linarith only [h226, h227, h343, h349, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                          · linarith only [h0, h226, h344, h352, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                            · linarith only [h0, h226, h344, h354, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h356 | h356
                              · linarith only [h0, h226, h315, h341, h343, h352, h356, hc23, hc34, hlam, hphi]
                              · linarith only [h226, h227, h343, h356, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h314, h343, hlam]
          · linarith only [h0, h226, h314, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h361 | h361
      · rcases m.htr 0 1 5 (by decide) (by decide) with h362 | h362
        · linarith only [h362, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h364 | h364
          · rcases m.htr 0 2 4 (by decide) (by decide) with h365 | h365
            · rcases m.htr 0 2 5 (by decide) (by decide) with h366 | h366
              · linarith only [h366, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h368 | h368
                · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
                  · linarith only [h364, h366, h369, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h371 | h371
                    · linarith only [h226, h361, h364, h366, h371, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h375 | h375
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
                              · linarith only [h226, h361, h369, h371, h373, h376, h377, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h380 | h380
                                  · linarith only [h226, h364, h369, h380, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h364, h366, h373, h376, h379, h380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h368, h369, h373, h376, h379, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h384 | h384
                              · linarith only [h361, h384, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                                  · linarith only [h226, h364, h376, h387, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                                    · linarith only [h226, h361, h362, h374, h376, h384, h389, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                    · linarith only [h364, h366, h386, h389, hc34, hc45, hlam, hphi]
                                · linarith only [h226, h368, h376, h386, hc23, hc35, hlam, hphi]
                          · linarith only [h226, h361, h368, h374, h375, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h365, h374, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h364, h373, hlam]
                · linarith only [h226, h361, h368, hlam]
            · linarith only [h0, h361, h365, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h398 | h398
            · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
              · linarith only [h399, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h401 | h401
                · rcases m.htr 0 3 5 (by decide) (by decide) with h402 | h402
                  · linarith only [h402, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                    · linarith only [h0, h361, h364, h402, h404, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                              · linarith only [h0, h361, h364, h402, h404, h406, h409, h410, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                                  · linarith only [h0, h364, h402, h406, h413, hc01, hc12, hlam, hphi]
                                  · linarith only [h0, h361, h364, h407, h409, h412, h413, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h361, h364, h401, h407, h412, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h417 | h417
                              · linarith only [h361, h417, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                                  · linarith only [h226, h361, h407, h409, h419, h420, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h422 | h422
                                    · linarith only [h361, h407, h417, h422, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h424 | h424
                                      · linarith only [h0, h361, h364, h406, h407, h409, h417, h419, h424, hlam]
                                      · linarith only [h0, h361, h364, h406, h407, h409, h419, h424, hc34, hc45, hlam, hphi]
                                · linarith only [h0, h361, h364, h401, h407, h419, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h0, h361, h364, h401, h406, h408, hlam]
                        · linarith only [h0, h364, h398, h402, h407, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h433 | h433
                              · linarith only [h0, h361, h364, h402, h406, h432, h433, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                                    · linarith only [h0, h361, h364, h402, h406, h430, h432, h433, h437, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                                      · linarith only [h0, h361, h364, h402, h430, h432, h433, h435, h439, hlam]
                                      · rcases h3bigk with h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h226, hlam, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h364, hlam, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h402, h406, h432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h402, hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          rcases p441_3 (m.d 0 3) (by simp) with h447 | h447
                                          · linarith only [h226, h447, hlam]
                                          · rcases p441_3 (m.d 1 3) (by simp) with h449 | h449
                                            · rcases p441_3 (m.d 2 3) (by simp) with h450 | h450
                                              · rcases p441_3 (m.d 3 4) (by simp) with h451 | h451
                                                · linarith only [h431, h451, hlam]
                                                · rcases p441_3 (m.d 3 5) (by simp) with h453 | h453
                                                  · linarith only [h432, h453, hlam]
                                                  · linarith only [h402, h453, hlam]
                                              · linarith only [h364, h450, hlam]
                                            · linarith only [h226, h449, hlam]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h406, hlam, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h401, h402, h432, hlam, p441_2]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h0, h364, h402, h406, hc01, hc23, hlam, hphi, ht12, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          rcases p441_3 (m.d 0 3) (by simp) with h462 | h462
                                          · linarith only [h364, h462, hlam]
                                          · rcases p441_3 (m.d 1 3) (by simp) with h464 | h464
                                            · linarith only [h406, h464, hlam]
                                            · linarith only [h226, h464, hlam]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h226, h361, h430, h435, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h0, h361, h406, h430, h435, hlam, p441_2]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h0, h361, h364, h402, h430, h435, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h401, hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h431, hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h435, hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h439, hlam, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h0, h361, h364, h430, h432, h435, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p441_1]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h432, hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [h436, hlam, p441_0]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          rcases p441_3 (m.d 0 3) (by simp) with h479 | h479
                                          · linarith only [h402, h479, hlam]
                                          · linarith only [h401, h479, hlam]
                                        · have p441_0 := h441c.1
                                          have p441_1 := h441c.2.1
                                          have p441_2 := h441c.2.2.1
                                          have p441_3 := h441c.2.2.2
                                          linarith only [hlam, p441_0]
                                  · linarith only [h406, h432, h436, hlam]
                                · linarith only [h406, h432, h435, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                              · linarith only [h0, h361, h364, h402, h404, h406, h432, h485, hc02, hc35, hlam, hphi, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                                  · linarith only [h0, h361, h406, h430, h432, h487, h488, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h361, h406, h430, h487, h488, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h0, h361, h406, h430, h487, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h361, h401, h406, h430, h431, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h398, h430, hlam]
                · linarith only [h226, h361, h401, hlam]
            · linarith only [h0, h361, h398, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h496 | h496
        · linarith only [h496, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h498 | h498
          · rcases m.htr 0 2 4 (by decide) (by decide) with h499 | h499
            · rcases m.htr 0 2 5 (by decide) (by decide) with h500 | h500
              · linarith only [h500, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h502 | h502
                · rcases m.htr 0 3 5 (by decide) (by decide) with h503 | h503
                  · linarith only [h498, h500, h503, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h505 | h505
                    · linarith only [h498, h500, h502, h505, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h508 | h508
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h513 | h513
                                  · linarith only [h361, h498, h502, h503, h513, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h498, h500, h507, h510, h512, h513, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h502, h503, h507, h510, h512, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h517 | h517
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
                                  · linarith only [h498, h503, h518, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h498, h500, h507, h510, h517, h518, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h502, h503, h507, h510, h517, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h522 | h522
                              · linarith only [h505, h509, h510, h522, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
                                  · linarith only [h498, h500, h510, h525, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                                    · linarith only [h499, h527, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                                    · linarith only [h498, h500, h524, h527, hc34, hc45, hlam, hphi]
                                · linarith only [h502, h503, h524, hc23, hc35, hlam, hphi]
                          · linarith only [h226, h502, h509, hlam]
                        · linarith only [h0, h499, h508, hlam]
                      · linarith only [h0, h498, h507, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
                  · linarith only [h499, h502, h534, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
                    · linarith only [h499, h500, h536, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h541 | h541
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h543 | h543
                                · linarith only [h498, h502, h543, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
                                  · linarith only [h499, h543, h545, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h547 | h547
                                    · linarith only [h499, h500, h538, h541, h545, h547, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                                      · linarith only [h499, h500, h543, h547, h549, hc23, hc34, hlam, hphi]
                                      · linarith only [h226, h502, h538, h540, h542, h549, hc01, hc12, hlam, hphi]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h552 | h552
                                · linarith only [h226, h498, h502, h552, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                                  · linarith only [h498, h554, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h556 | h556
                                    · linarith only [h226, h499, h500, h502, h538, h540, h541, h542, h554, h556, hc01, hc12, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                                      · linarith only [h540, h542, h558, hlam]
                                      · rcases h3bigk with h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h226, hlam, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h502, hc23, hc34, hlam, hphi, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h502, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h534, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          rcases p560_3 (m.d 0 3) (by simp) with h566 | h566
                                          · linarith only [h226, h566, hlam]
                                          · rcases p560_3 (m.d 1 3) (by simp) with h568 | h568
                                            · rcases p560_3 (m.d 2 3) (by simp) with h569 | h569
                                              · linarith only [h538, h569, hlam]
                                              · rcases p560_3 (m.d 3 4) (by simp) with h571 | h571
                                                · linarith only [h540, h571, hlam]
                                                · linarith only [h502, h571, hlam]
                                            · linarith only [h226, h568, hlam]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h498, h500, h541, h554, hlam, p560_2]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h226, h502, h538, hc01, hc12, hlam, hphi, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h498, h500, h538, h554, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h498, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h538, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h552, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h554, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h226, h538, h540, hc01, hc12, hlam, hphi, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h540, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h540, h542, hc23, hc45, hlam, hphi, ht34, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h558, hlam, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h226, h538, h541, hc01, hc12, hlam, hphi, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h541, hlam, p560_0]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          rcases p560_3 (m.d 0 3) (by simp) with h591 | h591
                                          · linarith only [h534, h591, hlam]
                                          · linarith only [h498, h591, hlam]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [h226, h502, h538, h541, hc01, hc12, hlam, hphi, p560_1]
                                        · have p560_0 := h560c.1
                                          have p560_1 := h560c.2.1
                                          have p560_2 := h560c.2.2.1
                                          have p560_3 := h560c.2.2.2
                                          linarith only [hlam, p560_0]
                            · linarith only [h226, h502, h540, h541, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h597 | h597
                            · linarith only [h540, h597, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h599 | h599
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                                · linarith only [h498, h540, h600, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h602 | h602
                                  · linarith only [h226, h498, h536, h540, h597, h599, h602, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht5b, u0elo2, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h604 | h604
                                    · linarith only [h499, h500, h536, h604, hlam]
                                    · linarith only [h499, h500, h540, h599, h600, h604, hc23, hc34, hlam, hphi]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h607 | h607
                                · linarith only [h498, h502, h607, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
                                  · linarith only [h499, h607, h609, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h611 | h611
                                    · linarith only [h226, h499, h500, h540, h599, h609, h611, hc01, hc35, hlam, hphi, ht12, ht23]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h613 | h613
                                      · linarith only [h499, h500, h607, h611, h613, hc23, hc34, hlam, hphi]
                                      · linarith only [h226, h540, h613, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h499, h500, h539, hc12, hc25, hlam, hphi]
                      · linarith only [h0, h498, h538, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h618 | h618
              · linarith only [h618, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
                · linarith only [h498, h499, h620, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h622 | h622
                  · linarith only [h498, h499, h622, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
                    · linarith only [h624, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h627 | h627
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h629 | h629
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h631 | h631
                                · linarith only [h498, h499, h620, h624, h626, h628, h630, h631, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                                  · linarith only [h498, h499, h624, h626, h628, h630, h633, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h635 | h635
                                    · linarith only [h498, h499, h624, h631, h635, hc23, hc34, hlam, hphi]
                                    · linarith only [h498, h499, h626, h628, h630, h635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h498, h499, h627, h630, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h226, h620, h628, h629, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h640 | h640
                            · linarith only [h628, h640, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                              · linarith only [h498, h499, h624, h628, h642, hc23, hc34, hlam, hphi]
                              · linarith only [h498, h499, h627, h642, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h645 | h645
                          · linarith only [h226, h620, h626, h627, h645, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h647 | h647
                            · linarith only [h645, h647, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
                              · linarith only [h498, h499, h624, h645, h649, hc23, hc34, hlam, hphi]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
                                · linarith only [h0, h498, h627, h649, h651, hc34, hc45, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
                                  · linarith only [h0, h498, h627, h647, h649, h653, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h655 | h655
                                    · linarith only [h0, h498, h627, h649, h651, h655, hc23, hc34, hlam, hphi]
                                    · linarith only [h498, h499, h655, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h498, h499, h626, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h659 | h659
            · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
              · linarith only [h498, h660, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h662 | h662
                · rcases m.htr 0 3 5 (by decide) (by decide) with h663 | h663
                  · linarith only [h663, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                    · linarith only [h665, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h673 | h673
                                  · linarith only [h498, h659, h663, h667, h672, h673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h498, h659, h667, h670, h672, h673, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h498, h662, h672, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                                  · linarith only [h667, h678, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · linarith only [h498, h659, h667, h670, h677, h678, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h498, h662, h677, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                              · linarith only [h665, h669, h670, h682, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h685 | h685
                                  · linarith only [h226, h670, h685, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h687 | h687
                                    · linarith only [h659, h682, h687, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h689 | h689
                                      · linarith only [h498, h659, h667, h670, h682, h684, h689, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                      · linarith only [h498, h659, h667, h670, h689, hc24, hc45, hlam, hphi]
                                · linarith only [h498, h659, h662, h684, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h498, h659, h662, h667, h669, hlam]
                        · linarith only [h498, h659, h667, h668, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h695 | h695
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h696 | h696
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h697 | h697
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h698 | h698
                              · linarith only [h665, h667, h695, h698, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h700 | h700
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h701 | h701
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h702 | h702
                                    · linarith only [h659, h698, h702, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h704 | h704
                                      · linarith only [h361, h698, h704, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · rcases h3bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h226, hlam, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h498, hlam, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h663, h667, h697, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h663, hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          rcases p706_3 (m.d 0 3) (by simp) with h712 | h712
                                          · linarith only [h226, h712, hlam]
                                          · rcases p706_3 (m.d 1 3) (by simp) with h714 | h714
                                            · rcases p706_3 (m.d 2 3) (by simp) with h715 | h715
                                              · rcases p706_3 (m.d 3 4) (by simp) with h716 | h716
                                                · linarith only [h696, h716, hlam]
                                                · rcases p706_3 (m.d 3 5) (by simp) with h718 | h718
                                                  · linarith only [h697, h718, hlam]
                                                  · linarith only [h663, h718, hlam]
                                              · linarith only [h498, h715, hlam]
                                            · linarith only [h226, h714, hlam]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h667, hlam, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h662, h663, h697, hlam, p706_2]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h498, h663, h667, hc02, hc23, hlam, hphi, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          rcases p706_3 (m.d 0 3) (by simp) with h727 | h727
                                          · linarith only [h498, h727, hlam]
                                          · rcases p706_3 (m.d 1 3) (by simp) with h729 | h729
                                            · linarith only [h667, h729, hlam]
                                            · linarith only [h226, h729, hlam]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h226, hc01, hc23, hlam, hphi, ht12, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h498, h659, h663, h667, h697, h700, hlam, p706_2]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h498, h659, h663, h700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h662, hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h696, hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h700, hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h704, hlam, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h498, h659, h697, h700, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p706_1]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h697, hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [h701, hlam, p706_0]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          rcases p706_3 (m.d 0 3) (by simp) with h744 | h744
                                          · linarith only [h663, h744, hlam]
                                          · linarith only [h662, h744, hlam]
                                        · have p706_0 := h706c.1
                                          have p706_1 := h706c.2.1
                                          have p706_2 := h706c.2.2.1
                                          have p706_3 := h706c.2.2.2
                                          linarith only [hlam, p706_0]
                                  · linarith only [h667, h697, h701, hlam]
                                · linarith only [h667, h697, h700, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
                              · linarith only [h665, h667, h695, h750, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                                  · linarith only [h0, h667, h697, h753, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h361, h667, h695, h753, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h361, h667, h695, h752, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h361, h662, h667, h695, h696, hlam]
                        · linarith only [h498, h659, h663, h695, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h498, h659, h662, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h760 | h760
              · linarith only [h760, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h762 | h762
                · rcases m.htr 0 3 5 (by decide) (by decide) with h763 | h763
                  · linarith only [h763, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h765 | h765
                    · linarith only [h762, h763, h765, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h767 | h767
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h768 | h768
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h770 | h770
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h771 | h771
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h772 | h772
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
                                  · linarith only [h762, h763, h767, h773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h498, h767, h770, h773, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h498, h762, h772, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h777 | h777
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h778 | h778
                                  · linarith only [h762, h763, h767, h778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h498, h767, h770, h778, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h498, h762, h777, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h782 | h782
                              · linarith only [h769, h770, h782, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h784 | h784
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h785 | h785
                                  · linarith only [h767, h770, h785, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h787 | h787
                                    · linarith only [h361, h782, h787, hc01, hc24, hlam, hphi, ht12]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
                                      · linarith only [h0, h659, h762, h768, h782, h789, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                      · rcases h3bigk with h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h226, hlam, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h498, hlam, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h498, h767, h770, h789, hc34, hc45, hlam, hphi, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h763, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h770, h789, hc03, hc45, hlam, hphi, ht34, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h770, h789, hc23, hc45, hlam, hphi, ht34, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h770, h789, hc34, hc45, hlam, hphi, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h770, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h762, h767, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h767, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h767, h770, h789, hc34, hc45, hlam, hphi, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h785, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h762, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h769, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h784, hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [hlam, p791_0]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h789, hlam, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h762, h789, hc34, hc45, hlam, hphi, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h0, h659, h768, h769, h789, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [h0, h498, h789, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p791_1]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          rcases p791_3 (m.d 0 3) (by simp) with h815 | h815
                                          · linarith only [h763, h815, hlam]
                                          · linarith only [h762, h815, hlam]
                                        · have p791_0 := h791c.1
                                          have p791_1 := h791c.2.1
                                          have p791_2 := h791c.2.2.1
                                          have p791_3 := h791c.2.2.2
                                          linarith only [hlam, p791_0]
                                · linarith only [h0, h498, h762, h784, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h498, h762, h767, h769, hlam]
                        · linarith only [h0, h498, h767, h768, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h822 | h822
                        · linarith only [h0, h659, h767, h822, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h824 | h824
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h825 | h825
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h827 | h827
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h828 | h828
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h829 | h829
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                                      · linarith only [h762, h763, h767, h825, h830, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                      · rcases h3bigk with h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c | h832c
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h226, hlam, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h498, hlam, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h763, h767, h824, h826, h830, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h763, hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          rcases p832_3 (m.d 0 3) (by simp) with h838 | h838
                                          · linarith only [h226, h838, hlam]
                                          · rcases p832_3 (m.d 1 3) (by simp) with h840 | h840
                                            · rcases p832_3 (m.d 2 3) (by simp) with h841 | h841
                                              · rcases p832_3 (m.d 3 4) (by simp) with h842 | h842
                                                · linarith only [h824, h842, hlam]
                                                · rcases p832_3 (m.d 3 5) (by simp) with h844 | h844
                                                  · linarith only [h825, h844, hlam]
                                                  · linarith only [h763, h844, hlam]
                                              · linarith only [h498, h841, hlam]
                                            · linarith only [h226, h840, hlam]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h767, hlam, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h762, h763, h824, h826, h830, hlam, p832_2]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h762, h763, h767, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          rcases p832_3 (m.d 0 3) (by simp) with h853 | h853
                                          · linarith only [h498, h853, hlam]
                                          · rcases p832_3 (m.d 1 3) (by simp) with h855 | h855
                                            · linarith only [h767, h855, hlam]
                                            · linarith only [h226, h855, hlam]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h824, h826, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p832_1, u5ehi4]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h762, h763, h767, h825, hlam, p832_2]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h762, h763, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h762, hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h824, hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h827, hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h830, hlam, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h762, h825, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p832_1]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h825, hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [h828, hlam, p832_0]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          rcases p832_3 (m.d 0 3) (by simp) with h870 | h870
                                          · linarith only [h763, h870, hlam]
                                          · linarith only [h762, h870, hlam]
                                        · have p832_0 := h832c.1
                                          have p832_1 := h832c.2.1
                                          have p832_2 := h832c.2.2.1
                                          have p832_3 := h832c.2.2.2
                                          linarith only [hlam, p832_0]
                                    · linarith only [h0, h822, h826, h829, hc01, hc14, hlam, hphi]
                                  · linarith only [h765, h767, h824, h826, h828, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                · linarith only [h762, h763, h767, h825, h827, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h877 | h877
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h878 | h878
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h879 | h879
                                    · linarith only [h0, h822, h826, h879, hc01, hc24, hlam, hphi, ht12]
                                    · linarith only [h0, h822, h879, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h0, h498, h825, h878, hc01, hc13, hlam, hphi]
                                · linarith only [h762, h763, h767, h825, h877, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h884 | h884
                              · linarith only [h765, h824, h825, h884, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h886 | h886
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h887 | h887
                                  · linarith only [h226, h825, h887, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h767, h887, hc01, hc35, hlam, hphi, ht12, ht23]
                                · linarith only [h0, h762, h767, h886, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h226, h762, h824, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h892 | h892
                  · linarith only [h892, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h894 | h894
                    · linarith only [h894, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h896 | h896
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h897 | h897
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h898 | h898
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h899 | h899
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h900 | h900
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h901 | h901
                                · linarith only [h226, h762, h896, h901, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h498, h898, h901, hc01, hc13, hlam, hphi]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h904 | h904
                                · linarith only [h0, h498, h762, h896, h904, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h498, h898, h900, h904, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h498, h762, h898, h899, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h908 | h908
                            · linarith only [h898, h908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h910 | h910
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h911 | h911
                                · linarith only [h226, h898, h911, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h913 | h913
                                  · linarith only [h896, h908, h913, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h915 | h915
                                    · linarith only [h0, h498, h762, h894, h897, h915, hc01, hc12, hlam, hphi]
                                    · linarith only [h0, h659, h898, h910, h915, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                                · linarith only [h0, h498, h762, h896, h918, hc01, hc12, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h920 | h920
                                  · linarith only [h892, h896, h920, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h922 | h922
                                    · linarith only [h897, h910, h922, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h924 | h924
                                      · linarith only [h0, h498, h896, h898, h910, h924, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h0, h498, h896, h898, h924, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h498, h896, h897, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h928 | h928
                        · linarith only [h0, h659, h896, h928, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h930 | h930
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h931 | h931
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h932 | h932
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h934 | h934
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h935 | h935
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h936 | h936
                                      · linarith only [h0, h498, h762, h894, h930, h936, hc01, hc13, hlam, hphi]
                                      · linarith only [h0, h498, h762, h932, h936, hc01, hc14, hlam, hphi]
                                    · linarith only [h928, h932, h935, hlam]
                                  · linarith only [h928, h932, h933, h934, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · linarith only [h896, h931, h933, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h942 | h942
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h943 | h943
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h944 | h944
                                    · linarith only [h361, h932, h944, hc01, hc24, hlam, hphi, ht12]
                                    · linarith only [h0, h928, h944, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h0, h498, h931, h943, hc01, hc13, hlam, hphi]
                                · linarith only [h896, h931, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h0, h498, h762, h930, h931, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
                            · linarith only [h930, h950, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h953 | h953
                                · linarith only [h226, h930, h953, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h896, h953, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h956 | h956
                                · linarith only [h0, h896, h930, h956, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h896, h956, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
