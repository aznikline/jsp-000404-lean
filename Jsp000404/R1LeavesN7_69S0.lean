import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_I_H_L_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h10, h12, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h11, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h10, h16, h2, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h16, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h4, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h3, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                · linarith only [h0, h2, h21, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h0, h2, h23, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h23, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h6, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
              · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                    · linarith only [h1, h27, h31, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h1, h28, h33, h34, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                          · linarith only [h0, h28, h36, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1, h33, h36, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h27, h33, h5, hc13, hc34, hlam, hphi]
                  · linarith only [h30, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h28, h29, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                · linarith only [h0, h2, h28, h42, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h0, h2, h28, h44, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h44, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h27, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
          · linarith only [h2, h3, h50, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
            · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
              · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h3, h54, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                    · linarith only [h1, h50, h57, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                        · linarith only [h0, h1, h50, h53, h59, h60, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h0, h53, h62, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h62, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h59, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h49, h56, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
              · linarith only [h2, h3, h53, hc12, hc24, hlam, hphi]
            · linarith only [h52, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h2, h49, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h70 | h70
      · rcases m.htr 0 2 5 (by decide) (by decide) with h71 | h71
        · rcases m.htr 0 3 4 (by decide) (by decide) with h72 | h72
          · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
            · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
              · linarith only [h0, h2, h74, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                            · linarith only [h0, h76, h82, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h82, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h2, h76, h80, h81, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h2, h72, h80, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h74, h79, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1, h72, h74, h76, h78, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h76, h77, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h2, h70, h76, hc12, hc23, hlam, hphi]
            · linarith only [h73, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h2, h70, h72, hlam]
        · linarith only [h71, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h94 | h94
        · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
          · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
            · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
              · linarith only [h0, h2, h94, h97, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                · linarith only [h0, h70, h99, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                              · linarith only [h1, h102, h107, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h107, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h101, h105, h106, h70, hc35, hlam, hphi, u5elo4]
                          · linarith only [h104, h105, h70, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h1, h101, h104, h2, h95, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h103, h96, hc13, hlam, hphi, ht34, ht45, u5elo0]
                    · linarith only [h1, h101, h102, h95, h97, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h101, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h96, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h117 | h117
            · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
              · linarith only [h0, h118, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                · linarith only [h0, h120, h70, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                    · linarith only [h1, h123, h95, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h127 | h127
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                              · rcases h2bigk with h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h122, h126, h127, h129, h2, h95, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p130_1]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h2, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h70, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h126, h127, h129, h2, h95, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p130_1]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h0, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h118, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h120, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h0, h127, h129, hc45, hlam, hphi, ht0b, ht5b, p130_1, u0elo0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  rcases p130_3 (m.d 0 2) (by simp) with h141 | h141
                                  · linarith only [h141, hlam, p130_0]
                                  · rcases p130_3 (m.d 1 2) (by simp) with h143 | h143
                                    · linarith only [h118, h143, hlam]
                                    · rcases p130_3 (m.d 2 3) (by simp) with h145 | h145
                                      · rcases p130_3 (m.d 2 4) (by simp) with h146 | h146
                                        · linarith only [h126, h146, hlam]
                                        · linarith only [h146, h70, hlam]
                                      · linarith only [h145, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  rcases p130_3 (m.d 0 2) (by simp) with h150 | h150
                                  · linarith only [h150, h2, hlam]
                                  · linarith only [h0, h150, hlam]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h126, h2, h95, hc02, hc23, hlam, hphi, p130_1]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h0, h122, h126, h2, h95, hlam, p130_2]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  rcases p130_3 (m.d 0 2) (by simp) with h156 | h156
                                  · linarith only [h156, hlam, p130_0]
                                  · rcases p130_3 (m.d 1 2) (by simp) with h158 | h158
                                    · linarith only [h120, h158, hlam]
                                    · rcases p130_3 (m.d 2 3) (by simp) with h160 | h160
                                      · rcases p130_3 (m.d 2 4) (by simp) with h161 | h161
                                        · rcases p130_3 (m.d 2 5) (by simp) with h162 | h162
                                          · linarith only [h128, h162, hlam]
                                          · rcases h3bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h118, h122, h127, h129, hc45, hlam, hphi, ht0b, ht5b, p164_1, u0elo2]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h2, hlam, p164_1]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h95, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h126, h129, h95, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h1, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h118, hlam, p164_1]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h123, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h1, h129, hc45, hlam, hphi, ht0b, ht5b, p164_1, u0elo0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              rcases p164_3 (m.d 0 3) (by simp) with h175 | h175
                                              · linarith only [h175, h2, hlam]
                                              · rcases p164_3 (m.d 1 3) (by simp) with h177 | h177
                                                · linarith only [h118, h177, hlam]
                                                · rcases p164_3 (m.d 2 3) (by simp) with h179 | h179
                                                  · rcases p164_3 (m.d 3 4) (by simp) with h180 | h180
                                                    · linarith only [h126, h180, hlam]
                                                    · linarith only [h180, h95, hlam]
                                                  · linarith only [h179, h2, hlam]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              rcases p164_3 (m.d 0 3) (by simp) with h184 | h184
                                              · linarith only [h184, h2, hlam]
                                              · linarith only [h1, h184, hlam]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h0, h122, h127, h129, h2, h95, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h0, h122, h126, h127, h2, h95, hlam, p164_2]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h0, h122, h126, h127, h129, h2, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h118, h122, h126, h127, h129, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p164_1]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h126, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              rcases p164_3 (m.d 0 3) (by simp) with h194 | h194
                                              · linarith only [h194, h95, hlam]
                                              · linarith only [h117, h194, hlam]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h117, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h125, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h127, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [h129, hlam, p164_0]
                                            · have p164_0 := h164c.1
                                              have p164_1 := h164c.2.1
                                              have p164_2 := h164c.2.2.1
                                              have p164_3 := h164c.2.2.2
                                              linarith only [hlam, p164_0]
                                        · linarith only [h161, hlam, p130_0]
                                      · linarith only [h160, h2, hlam]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  rcases p130_3 (m.d 0 2) (by simp) with h204 | h204
                                  · linarith only [h204, h70, hlam]
                                  · linarith only [h0, h204, hlam]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h126, hlam, p130_1]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  rcases p130_3 (m.d 0 2) (by simp) with h209 | h209
                                  · linarith only [h209, h70, hlam]
                                  · linarith only [h209, h94, hlam]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h94, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h122, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h127, hlam, p130_1]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [h128, hlam, p130_0]
                                · have p130_0 := h130c.1
                                  have p130_1 := h130c.2.1
                                  have p130_2 := h130c.2.2.1
                                  have p130_3 := h130c.2.2.2
                                  linarith only [hlam, p130_0]
                              · linarith only [h129, h95, hc04, hlam, hphi, ht45, u5elo4]
                            · linarith only [h128, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h126, h127, h2, h95, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h220 | h220
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h221 | h221
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h222 | h222
                              · rcases h2bigk with h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h122, h220, h222, hc45, hlam, hphi, ht0b, ht5b, p223_1, u0elo1]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h2, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h70, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h126, h2, h220, h222, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p223_1]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h0, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h118, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h120, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h0, h220, h222, hc45, hlam, hphi, ht0b, ht5b, p223_1, u0elo0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h126, hc02, hc34, hlam, hphi, ht23, p223_1]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h126, hc12, hc34, hlam, hphi, ht23, p223_1]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h126, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  rcases p223_3 (m.d 0 2) (by simp) with h238 | h238
                                  · linarith only [h2, h238, hlam]
                                  · linarith only [h238, h94, hlam]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  rcases p223_3 (m.d 0 2) (by simp) with h241 | h241
                                  · linarith only [h241, hlam, p223_0]
                                  · rcases p223_3 (m.d 1 2) (by simp) with h243 | h243
                                    · linarith only [h120, h243, hlam]
                                    · rcases p223_3 (m.d 2 3) (by simp) with h245 | h245
                                      · linarith only [h126, h245, hlam]
                                      · linarith only [h2, h245, hlam]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  rcases p223_3 (m.d 0 2) (by simp) with h248 | h248
                                  · linarith only [h248, h70, hlam]
                                  · linarith only [h0, h248, hlam]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h126, h2, hc02, hc34, hlam, hphi, ht23, p223_1]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  rcases p223_3 (m.d 0 2) (by simp) with h253 | h253
                                  · linarith only [h253, h70, hlam]
                                  · linarith only [h253, h94, hlam]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h94, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h122, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h220, hlam, p223_1]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [h221, hlam, p223_0]
                                · have p223_0 := h223c.1
                                  have p223_1 := h223c.2.1
                                  have p223_2 := h223c.2.2.1
                                  have p223_3 := h223c.2.2.2
                                  linarith only [hlam, p223_0]
                              · linarith only [h222, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h221, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2, h220, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h117, h125, hc13, hlam, hphi, ht34, ht45, u5elo0]
                  · linarith only [h122, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h117, h2, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h94, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h268 | h268
    · linarith only [h0, h1, h268, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h270 | h270
      · rcases m.htr 0 2 5 (by decide) (by decide) with h271 | h271
        · rcases m.htr 0 3 4 (by decide) (by decide) with h272 | h272
          · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
            · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
              · linarith only [h0, h268, h274, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                            · linarith only [h0, h1, h274, h276, h282, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h280, h282, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1, h274, h276, h280, h281, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h274, h276, h280, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h273, h276, h279, hc24, hlam, hphi, ht45, u5elo0]
                    · linarith only [h0, h1, h276, h278, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h276, h277, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h1, h270, h274, h276, hc12, hc23, hlam, hphi]
            · linarith only [h1, h273, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h1, h270, h272, hlam]
        · linarith only [h271, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h294 | h294
        · rcases m.htr 0 3 4 (by decide) (by decide) with h295 | h295
          · rcases m.htr 0 3 5 (by decide) (by decide) with h296 | h296
            · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
              · linarith only [h0, h268, h297, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                · linarith only [h0, h270, h299, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h303 | h303
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h305 | h305
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h306 | h306
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                              · rcases h2bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h270, hc12, hc24, hlam, hphi, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h268, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h270, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h313 | h313
                                  · rcases p308_3 (m.d 1 2) (by simp) with h314 | h314
                                    · linarith only [h0, h314, hlam]
                                    · linarith only [h301, h314, hlam]
                                  · linarith only [h313, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h0, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h297, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h299, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h0, h305, h307, hc45, hlam, hphi, ht0b, ht5b, p308_1, u0elo0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h323 | h323
                                  · linarith only [h323, hlam, p308_0]
                                  · rcases p308_3 (m.d 1 2) (by simp) with h325 | h325
                                    · linarith only [h297, h325, hlam]
                                    · rcases p308_3 (m.d 2 3) (by simp) with h327 | h327
                                      · rcases p308_3 (m.d 2 4) (by simp) with h328 | h328
                                        · linarith only [h304, h328, hlam]
                                        · linarith only [h270, h328, hlam]
                                      · linarith only [h327, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h332 | h332
                                  · linarith only [h268, h332, hlam]
                                  · linarith only [h0, h332, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h270, hc02, hc23, hlam, hphi, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h0, h1, h297, h301, hlam, p308_2]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h338 | h338
                                  · linarith only [h338, hlam, p308_0]
                                  · rcases p308_3 (m.d 1 2) (by simp) with h340 | h340
                                    · linarith only [h299, h340, hlam]
                                    · rcases p308_3 (m.d 2 3) (by simp) with h342 | h342
                                      · rcases p308_3 (m.d 2 4) (by simp) with h343 | h343
                                        · rcases p308_3 (m.d 2 5) (by simp) with h344 | h344
                                          · linarith only [h306, h344, hlam]
                                          · rcases h3bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h1, hlam, p346_1]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h268, hlam, p346_1]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h307, hc45, hlam, hphi, ht0b, ht5b, p346_1, u0elo2]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              rcases p346_3 (m.d 0 3) (by simp) with h351 | h351
                                              · rcases p346_3 (m.d 1 3) (by simp) with h352 | h352
                                                · rcases p346_3 (m.d 2 3) (by simp) with h353 | h353
                                                  · rcases p346_3 (m.d 3 4) (by simp) with h354 | h354
                                                    · linarith only [h295, h354, hlam]
                                                    · linarith only [h307, h354, hlam]
                                                  · linarith only [h305, h353, hlam]
                                                · linarith only [h303, h352, hlam]
                                              · linarith only [h351, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h0, h1, h297, hc12, hc23, hlam, hphi, p346_1]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h297, hlam, p346_1]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              rcases p346_3 (m.d 0 3) (by simp) with h363 | h363
                                              · linarith only [h1, h363, hlam]
                                              · linarith only [h295, h363, hlam]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h0, h1, h301, h305, hlam, p346_2]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h0, h1, h301, h305, h307, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h0, h1, h301, h305, h307, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p346_1]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              rcases p346_3 (m.d 0 3) (by simp) with h370 | h370
                                              · linarith only [h268, h370, hlam]
                                              · linarith only [h295, h370, hlam]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h0, h301, h304, h305, hlam, p308_1, p346_2]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h295, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h302, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h304, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h295, h307, hc45, hlam, hphi, ht0b, ht5b, p346_1, u0elo2]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h296, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h303, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h305, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [h307, hlam, p346_0]
                                            · have p346_0 := h346c.1
                                              have p346_1 := h346c.2.1
                                              have p346_2 := h346c.2.2.1
                                              have p346_3 := h346c.2.2.2
                                              linarith only [hlam, p346_0]
                                        · linarith only [h343, hlam, p308_0]
                                      · linarith only [h268, h342, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h386 | h386
                                  · linarith only [h270, h386, hlam]
                                  · linarith only [h0, h386, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h304, hlam, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  rcases p308_3 (m.d 0 2) (by simp) with h391 | h391
                                  · linarith only [h270, h391, hlam]
                                  · linarith only [h294, h391, hlam]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h294, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h301, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h305, hlam, p308_1]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [h306, hlam, p308_0]
                                · have p308_0 := h308c.1
                                  have p308_1 := h308c.2.1
                                  have p308_2 := h308c.2.2.1
                                  have p308_3 := h308c.2.2.2
                                  linarith only [hlam, p308_0]
                              · linarith only [h307, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h306, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1, h297, h305, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h297, h301, h304, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h296, h301, h303, hc25, hlam, hphi, u5elo0]
                    · linarith only [h0, h1, h301, h302, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h301, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h296, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
            · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
              · linarith only [h0, h268, h294, h408, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                · linarith only [h0, h270, h410, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h1, h295, h408, h413, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h412, h413, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h412, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1, h407, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h294, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

end R2N4
