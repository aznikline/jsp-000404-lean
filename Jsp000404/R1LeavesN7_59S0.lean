import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3546000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_R_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
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
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h10, h12, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                          · linarith only [h0, h10, h16, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h0, h16, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h19, h21, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h19, h23, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                          · linarith only [h1, h25, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h0, h25, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                · linarith only [h29, h7, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                    · linarith only [h0, h32, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                      · linarith only [h0, h32, h34, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h32, h36, h4, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                          · linarith only [h1, h38, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h29, h32, h34, h38, h4, h40, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                              · linarith only [h0, h34, h42, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h31, h38, h42, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h45, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                      · linarith only [h0, h4, h45, h47, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h0, h4, h45, h49, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                          · linarith only [h1, h51, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h0, h29, h47, h5, h51, h53, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h31, h47, h5, h55, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                                · linarith only [h4, h57, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                                  · linarith only [h29, h4, h59, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                                    · linarith only [h31, h5, h61, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                                      · linarith only [h31, h4, h45, h63, h7, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h4, h45, h63, h7, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h66 | h66
              · rcases m.htr 0 3 5 (by decide) (by decide) with h67 | h67
                · linarith only [h4, h6, h67, hlam]
                · linarith only [h66, h67, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
                · linarith only [h66, h70, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
                  · linarith only [h5, h6, h72, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
                    · linarith only [h0, h74, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h4, h6, h74, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h77 | h77
            · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
              · linarith only [h4, h5, h78, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
                · linarith only [h78, h80, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h83, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h4, h5, h83, hc12, hc24, hlam, hphi]
                  · linarith only [h4, h5, h82, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
              · linarith only [h4, h5, h87, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h89 | h89
                · linarith only [h87, h89, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                    · linarith only [h0, h92, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h4, h77, h92, hc12, hc25, hlam, hphi]
                  · linarith only [h4, h5, h91, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
          · rcases m.htr 0 2 5 (by decide) (by decide) with h97 | h97
            · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
              · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
                · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                    · linarith only [h100, h101, h4, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h0, h104, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h104, h4, h97, hc12, hc23, hlam, hphi]
                      · linarith only [h103, h4, h96, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                    · linarith only [h108, h4, h97, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                        · linarith only [h1, h108, h111, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h111, h4, h97, hc12, hc23, hlam, hphi]
                      · linarith only [h110, h4, h96, hc12, hc23, hlam, hphi]
                · linarith only [h98, h99, hc35, hlam, hphi, u3ehi3]
              · linarith only [h4, h96, h98, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
              · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
                · rcases m.htr 0 4 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h119, h96, h97, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                    · linarith only [h0, h121, h4, h96, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                        · linarith only [h0, h124, h97, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                          · linarith only [h1, h126, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h117, h126, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h123, h4, h96, hc12, hc23, hlam, hphi]
                · linarith only [h117, h118, hc35, hlam, hphi, u3ehi3]
              · linarith only [h117, h4, h96, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h132 | h132
            · rcases m.htr 0 3 4 (by decide) (by decide) with h133 | h133
              · rcases m.htr 0 3 5 (by decide) (by decide) with h134 | h134
                · rcases m.htr 0 4 5 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
                    · linarith only [h132, h136, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                      · linarith only [h1, h132, h136, h138, h96, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h1, h136, h140, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                        · linarith only [h132, h140, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h132, h135, h96, hlam]
                · linarith only [h133, h134, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h145 | h145
                · linarith only [h133, h145, hc34, hlam, hphi, u3ehi4]
                · linarith only [h132, h145, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
              · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
                · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                    · linarith only [h0, h151, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                      · linarith only [h0, h153, h96, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                        · linarith only [h0, h132, h155, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                          · linarith only [h1, h157, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h148, h157, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                    · linarith only [h0, h148, h160, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                      · linarith only [h0, h162, h96, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
                        · linarith only [h0, h132, h164, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                          · linarith only [h1, h166, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h148, h166, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · linarith only [h148, h149, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
                · linarith only [h148, h170, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h173, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h175 | h175
                      · linarith only [h0, h175, h96, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h0, h132, h177, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                          · linarith only [h1, h148, h179, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                            · linarith only [h1, h181, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                              · linarith only [h183, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                              · linarith only [h172, h179, h183, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                    · linarith only [h0, h186, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h0, h188, h96, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                        · linarith only [h0, h132, h190, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                          · linarith only [h1, h192, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
                            · linarith only [h170, h192, h194, h2, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                              · linarith only [h172, h196, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                                      · linarith only [h1, h148, h172, h201, hc34, hlam, hphi, u3ehi1]
                                      · linarith only [h1, h148, h198, h200, h201, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                    · linarith only [h1, h148, h198, h200, hc45, hlam, hphi, ht34, u3ehi1]
                                  · linarith only [h1, h148, h198, h199, hc35, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                                  · linarith only [h198, h206, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                                    · linarith only [h1, h148, h172, h198, h208, hc34, hlam, hphi, u3ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                                      · linarith only [h198, h208, h210, hc34, hlam, hphi, u3ehi2]
                                      · linarith only [h1, h148, h210, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
        · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
          · rcases m.htr 0 2 5 (by decide) (by decide) with h215 | h215
            · linarith only [h0, h215, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
                · linarith only [h0, h213, h218, h3, hlam]
                · linarith only [h217, h218, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h221 | h221
                · linarith only [h217, h221, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
                  · linarith only [h0, h214, h223, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
                    · linarith only [h0, h225, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h213, h215, h225, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h228 | h228
            · linarith only [h0, h228, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h230 | h230
              · linarith only [h213, h214, h230, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
                · linarith only [h230, h232, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
                  · linarith only [h2, h234, h3, hlam]
                  · linarith only [h213, h214, h234, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h237 | h237
          · rcases m.htr 0 2 5 (by decide) (by decide) with h238 | h238
            · linarith only [h0, h238, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h240 | h240
              · rcases m.htr 0 3 5 (by decide) (by decide) with h241 | h241
                · linarith only [h1, h241, h3, hlam]
                · linarith only [h240, h241, hc35, hlam, hphi, u3ehi3]
              · linarith only [h213, h237, h240, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
            · linarith only [h0, h245, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h247 | h247
              · rcases m.htr 0 3 5 (by decide) (by decide) with h248 | h248
                · linarith only [h1, h248, h3, hlam]
                · linarith only [h247, h248, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h251 | h251
                · linarith only [h247, h251, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
                  · linarith only [h2, h253, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                    · linarith only [h0, h255, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                      · linarith only [h0, h237, h257, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                        · linarith only [h0, h1, h245, h259, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                          · linarith only [h1, h261, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h263 | h263
                            · linarith only [h2, h213, h251, h259, h261, h263, h3, hc02, hc25, hlam, hphi]
                            · linarith only [h2, h261, h263, h3, hc35, hlam, hphi, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h266 | h266
      · rcases m.htr 0 2 3 (by decide) (by decide) with h267 | h267
        · rcases m.htr 0 2 4 (by decide) (by decide) with h268 | h268
          · linarith only [h0, h2, h268, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h270 | h270
            · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
              · linarith only [h1, h2, h271, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
                · linarith only [h271, h273, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                    · linarith only [h0, h2, h276, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h267, h268, h276, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h267, h275, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h280 | h280
              · linarith only [h0, h2, h267, h280, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                · linarith only [h280, h282, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                    · linarith only [h0, h285, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h267, h268, h285, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h266, h267, h270, h284, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h289 | h289
          · linarith only [h0, h2, h289, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h291 | h291
            · rcases m.htr 0 3 4 (by decide) (by decide) with h292 | h292
              · linarith only [h1, h2, h292, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h294 | h294
                · linarith only [h292, h294, hc34, hlam, hphi, u3ehi4]
                · linarith only [h267, h291, h294, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
              · linarith only [h1, h2, h297, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
                · linarith only [h297, h299, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                    · linarith only [h0, h267, h302, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                      · linarith only [h0, h1, h2, h289, h304, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                        · linarith only [h0, h291, h306, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h308 | h308
                          · linarith only [h1, h308, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h1, h2, h308, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h1, h2, h301, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h312 | h312
        · rcases m.htr 0 2 4 (by decide) (by decide) with h313 | h313
          · linarith only [h0, h2, h313, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h315 | h315
            · linarith only [h0, h266, h315, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h317 | h317
              · linarith only [h0, h2, h312, h317, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h319 | h319
                · linarith only [h317, h319, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
                    · linarith only [h0, h266, h321, h322, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                    · linarith only [h312, h313, h322, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h312, h321, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h326 | h326
          · linarith only [h1, h2, h312, h326, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
            · linarith only [h1, h266, h312, h328, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h330 | h330
              · linarith only [h1, h2, h330, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
                · linarith only [h330, h332, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
                    · linarith only [h0, h312, h335, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                      · linarith only [h0, h326, h334, h337, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                        · linarith only [h1, h2, h328, h335, h337, h339, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h341 | h341
                          · linarith only [h1, h2, h330, h337, h341, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h1, h2, h341, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h1, h2, h334, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
    · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
      · rcases m.htr 0 2 3 (by decide) (by decide) with h347 | h347
        · linarith only [h0, h1, h347, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h349 | h349
          · rcases m.htr 0 2 5 (by decide) (by decide) with h350 | h350
            · rcases m.htr 0 3 4 (by decide) (by decide) with h351 | h351
              · rcases m.htr 0 3 5 (by decide) (by decide) with h352 | h352
                · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
                    · linarith only [h347, h350, h354, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                        · linarith only [h0, h1, h354, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h350, h354, h357, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h349, h354, h356, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h361 | h361
                    · linarith only [h0, h361, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                        · linarith only [h0, h1, h361, h364, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h350, h361, h364, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h349, h361, h363, hc12, hc23, hlam, hphi]
                · linarith only [h351, h352, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h345, h351, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 3 5 (by decide) (by decide) with h371 | h371
                · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
                  · linarith only [h349, h350, h372, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h374 | h374
                    · linarith only [h0, h374, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                        · linarith only [h0, h1, h349, h350, h370, h374, h377, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h345, h372, h381, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                                · linarith only [h1, h346, h374, h376, h377, h383, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h345, h346, h374, h377, h379, h383, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h1, h346, h376, h377, h379, h380, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1, h346, h376, h377, h379, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h349, h350, h376, hc12, hc25, hlam, hphi]
                · linarith only [h370, h371, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h345, h370, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
            · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                    · linarith only [h347, h391, h395, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                      · linarith only [h0, h1, h349, h395, h397, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
                        · linarith only [h1, h345, h395, h397, h399, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h349, h391, h399, hc12, hc24, hlam, hphi]
                  · linarith only [h349, h391, h394, hlam]
                · linarith only [h392, h393, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h345, h392, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
              · rcases m.htr 0 3 5 (by decide) (by decide) with h406 | h406
                · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                    · linarith only [h0, h408, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                      · linarith only [h0, h1, h349, h408, h410, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
                        · linarith only [h0, h391, h412, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
                              · linarith only [h1, h345, h408, h416, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h1, h345, h407, h408, h410, h416, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h345, h407, h415, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h1, h345, h405, h407, h414, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · linarith only [h0, h1, h421, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                      · linarith only [h0, h349, h423, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h425 | h425
                        · linarith only [h0, h391, h425, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                              · linarith only [h1, h345, h407, h421, h429, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h431 | h431
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h434 | h434
                                      · linarith only [h345, h407, h427, h434, hlam]
                                      · rcases h2bigk with h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c | h436c
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h0, h1, h421, hc12, hc23, hlam, hphi, p436_1]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h347, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h349, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h391, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h0, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h421, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h423, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h425, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          rcases p436_3 (m.d 0 2) (by simp) with h447 | h447
                                          · linarith only [h447, hlam, p436_0]
                                          · rcases p436_3 (m.d 1 2) (by simp) with h449 | h449
                                            · linarith only [h421, h449, hlam]
                                            · rcases p436_3 (m.d 2 3) (by simp) with h451 | h451
                                              · rcases p436_3 (m.d 2 4) (by simp) with h452 | h452
                                                · linarith only [h431, h452, hlam]
                                                · linarith only [h349, h452, hlam]
                                              · linarith only [h451, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          rcases p436_3 (m.d 0 2) (by simp) with h456 | h456
                                          · linarith only [h347, h456, hlam]
                                          · linarith only [h0, h456, hlam]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h349, h407, h433, hc02, hc23, hlam, hphi, p436_1]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h345, h407, h427, h433, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u3ehi3]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          rcases p436_3 (m.d 0 2) (by simp) with h462 | h462
                                          · linarith only [h462, hlam, p436_0]
                                          · rcases p436_3 (m.d 1 2) (by simp) with h464 | h464
                                            · linarith only [h423, h464, hlam]
                                            · rcases p436_3 (m.d 2 3) (by simp) with h466 | h466
                                              · rcases p436_3 (m.d 2 4) (by simp) with h467 | h467
                                                · rcases p436_3 (m.d 2 5) (by simp) with h468 | h468
                                                  · linarith only [h433, h468, hlam]
                                                  · linarith only [h391, h468, hlam]
                                                · linarith only [h467, hlam, p436_0]
                                              · linarith only [h347, h466, hlam]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          rcases p436_3 (m.d 0 2) (by simp) with h473 | h473
                                          · linarith only [h349, h473, hlam]
                                          · linarith only [h0, h473, hlam]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h431, hlam, p436_1]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h345, h407, h427, h433, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p436_1, u3ehi3]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          rcases p436_3 (m.d 0 2) (by simp) with h479 | h479
                                          · linarith only [h479, hlam, p436_0]
                                          · rcases p436_3 (m.d 1 2) (by simp) with h481 | h481
                                            · linarith only [h425, h481, hlam]
                                            · rcases p436_3 (m.d 2 3) (by simp) with h483 | h483
                                              · rcases p436_3 (m.d 2 4) (by simp) with h484 | h484
                                                · rcases p436_3 (m.d 2 5) (by simp) with h485 | h485
                                                  · rcases h5bigk with h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h428, h434, hlam, hphi, ht0b, ht34, ht45, ht5b, p486_1, u0elo4, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h391, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h1, h346, h421, h434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h407, hlam, p486_1]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h346, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h425, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h1, h346, h421, h434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h429, hlam, p486_1]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      rcases p486_3 (m.d 0 5) (by simp) with h497 | h497
                                                      · linarith only [h391, h497, hlam]
                                                      · rcases p486_3 (m.d 1 5) (by simp) with h499 | h499
                                                        · linarith only [h425, h499, hlam]
                                                        · rcases p486_3 (m.d 2 5) (by simp) with h501 | h501
                                                          · rcases p486_3 (m.d 3 5) (by simp) with h502 | h502
                                                            · linarith only [h432, h502, hlam]
                                                            · rcases p486_3 (m.d 4 5) (by simp) with h504 | h504
                                                              · linarith only [h433, h504, hlam]
                                                              · linarith only [h407, h504, hlam]
                                                          · linarith only [h391, h501, hlam]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      rcases p486_3 (m.d 0 5) (by simp) with h508 | h508
                                                      · linarith only [h391, h508, hlam]
                                                      · linarith only [h346, h508, hlam]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      rcases p486_3 (m.d 0 5) (by simp) with h512 | h512
                                                      · linarith only [h391, h512, hlam]
                                                      · linarith only [h406, h512, hlam]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h345, h407, h427, h431, h433, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h406, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h428, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h432, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h434, hlam, p486_1]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h406, h434, hc45, hlam, hphi, ht34, p486_1, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h428, h434, hc45, hlam, hphi, ht34, p486_1, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h433, hlam, p486_0]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [h431, h433, h434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u3ehi3]
                                                    · have p486_0 := h486c.1
                                                      have p486_1 := h486c.2.1
                                                      have p486_2 := h486c.2.2.1
                                                      have p486_3 := h486c.2.2.2
                                                      linarith only [hlam, p486_0]
                                                  · linarith only [h485, hlam, p436_0]
                                                · linarith only [h349, h484, hlam]
                                              · linarith only [h347, h483, hlam]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          rcases p436_3 (m.d 0 2) (by simp) with h529 | h529
                                          · linarith only [h391, h529, hlam]
                                          · linarith only [h0, h529, hlam]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h432, hlam, p436_1]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [h433, hlam, p436_0]
                                        · have p436_0 := h436c.1
                                          have p436_1 := h436c.2.1
                                          have p436_2 := h436c.2.2.1
                                          have p436_3 := h436c.2.2.2
                                          linarith only [hlam, p436_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h535 | h535
                                      · linarith only [h1, h345, h421, h427, h433, h535, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                      · rcases h2bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h349, hc12, hc24, hlam, hphi, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h347, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h349, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h391, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h0, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h421, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h423, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h425, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          rcases p537_3 (m.d 0 2) (by simp) with h548 | h548
                                          · linarith only [h548, hlam, p537_0]
                                          · rcases p537_3 (m.d 1 2) (by simp) with h550 | h550
                                            · linarith only [h421, h550, hlam]
                                            · rcases p537_3 (m.d 2 3) (by simp) with h552 | h552
                                              · rcases p537_3 (m.d 2 4) (by simp) with h553 | h553
                                                · linarith only [h431, h553, hlam]
                                                · linarith only [h349, h553, hlam]
                                              · linarith only [h552, hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          rcases p537_3 (m.d 0 2) (by simp) with h557 | h557
                                          · linarith only [h347, h557, hlam]
                                          · linarith only [h0, h557, hlam]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h349, hc02, hc23, hlam, hphi, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h0, h391, hc12, hc23, hlam, hphi, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h0, h1, h346, h421, h427, h429, h433, hc12, hc23, hc45, hlam, hphi, ht34, p537_1, u3ehi3]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h1, h346, h421, h427, h429, h433, hc12, hc23, hc45, hlam, hphi, ht34, p537_1, u3ehi3]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h431, hlam, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [hlam, p537_0]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h433, hlam, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          rcases p537_3 (m.d 0 2) (by simp) with h568 | h568
                                          · linarith only [h568, hlam, p537_0]
                                          · rcases p537_3 (m.d 1 2) (by simp) with h570 | h570
                                            · linarith only [h425, h570, hlam]
                                            · rcases p537_3 (m.d 2 3) (by simp) with h572 | h572
                                              · rcases p537_3 (m.d 2 4) (by simp) with h573 | h573
                                                · linarith only [h433, h573, hlam]
                                                · linarith only [h349, h573, hlam]
                                              · linarith only [h347, h572, hlam]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          rcases p537_3 (m.d 0 2) (by simp) with h577 | h577
                                          · linarith only [h391, h577, hlam]
                                          · linarith only [h0, h577, hlam]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h432, hlam, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [h0, h349, hc12, hc25, hlam, hphi, p537_1]
                                        · have p537_0 := h537c.1
                                          have p537_1 := h537c.2.1
                                          have p537_2 := h537c.2.2.1
                                          have p537_3 := h537c.2.2.2
                                          linarith only [hlam, p537_0]
                                  · linarith only [h1, h346, h421, h427, h429, h432, hc35, hlam, hphi, u3ehi3]
                                · linarith only [h1, h346, h421, h427, h429, h431, hlam]
                            · linarith only [h1, h346, h428, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h346, h427, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h405, h406, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h345, h405, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h589 | h589
        · linarith only [h0, h1, h589, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h591 | h591
          · rcases m.htr 0 2 5 (by decide) (by decide) with h592 | h592
            · linarith only [h0, h346, h592, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h594 | h594
              · rcases m.htr 0 3 5 (by decide) (by decide) with h595 | h595
                · rcases m.htr 0 4 5 (by decide) (by decide) with h596 | h596
                  · linarith only [h0, h346, h591, h596, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                    · linarith only [h0, h589, h598, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
                        · linarith only [h0, h1, h592, h598, h601, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h604 | h604
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h605 | h605
                              · linarith only [h345, h346, h598, h604, h605, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h0, h346, h600, h605, hc24, hc45, hlam, hphi]
                            · linarith only [h595, h604, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h0, h1, h603, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h591, h598, h600, hc12, hc23, hlam, hphi]
                · linarith only [h594, h595, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h345, h594, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h613 | h613
            · linarith only [h345, h346, h591, h613, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h615 | h615
              · rcases m.htr 0 3 5 (by decide) (by decide) with h616 | h616
                · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
                  · linarith only [h345, h346, h617, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                    · linarith only [h0, h589, h619, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
                      · linarith only [h0, h591, h621, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
                        · linarith only [h0, h1, h613, h619, h623, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h627 | h627
                              · linarith only [h345, h346, h591, h617, h619, h626, h627, hc02, hc23, hlam, hphi]
                              · linarith only [h345, h346, h625, h627, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h616, h626, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h0, h1, h625, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h615, h616, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h345, h615, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h634 | h634
      · rcases m.htr 0 2 3 (by decide) (by decide) with h635 | h635
        · linarith only [h0, h1, h635, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h637 | h637
          · linarith only [h0, h345, h637, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h639 | h639
            · rcases m.htr 0 3 4 (by decide) (by decide) with h640 | h640
              · rcases m.htr 0 3 5 (by decide) (by decide) with h641 | h641
                · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
                    · linarith only [h635, h639, h643, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                      · linarith only [h0, h1, h637, h639, h643, h645, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h647 | h647
                        · linarith only [h0, h1, h643, h647, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h639, h643, h647, hc12, hc23, hlam, hphi]
                  · linarith only [h345, h634, h642, hlam]
                · linarith only [h640, h641, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h652 | h652
                · linarith only [h640, h652, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1, h639, h652, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h655 | h655
              · rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
                · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
                    · linarith only [h0, h345, h655, h658, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
                      · linarith only [h0, h1, h637, h658, h660, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h662 | h662
                        · linarith only [h0, h1, h639, h658, h662, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h665 | h665
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h668 | h668
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h669 | h669
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h670 | h670
                                      · linarith only [h655, h670, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                      · linarith only [h655, h657, h670, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                    · linarith only [h345, h634, h660, h666, h669, hlam]
                                  · linarith only [h345, h634, h658, h664, h665, h668, hlam]
                                · linarith only [h345, h634, h658, h662, h664, h667, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h345, h634, h665, h666, hc45, hlam, hphi, ht34, u3ehi4]
                            · linarith only [h345, h634, h664, h665, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h655, h664, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h345, h634, h657, hlam]
                · linarith only [h655, h656, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h681 | h681
                · linarith only [h655, h681, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h634, h681, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h684 | h684
        · linarith only [h0, h1, h684, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h686 | h686
          · linarith only [h0, h345, h686, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h688 | h688
            · linarith only [h0, h634, h688, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h690 | h690
              · rcases m.htr 0 3 5 (by decide) (by decide) with h691 | h691
                · rcases m.htr 0 4 5 (by decide) (by decide) with h692 | h692
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h693 | h693
                    · linarith only [h0, h684, h693, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h695 | h695
                      · linarith only [h0, h686, h692, h695, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h697 | h697
                        · linarith only [h0, h688, h697, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h699 | h699
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h700 | h700
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h701 | h701
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h702 | h702
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h703 | h703
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h704 | h704
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h705 | h705
                                      · linarith only [h690, h705, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                      · linarith only [h690, h692, h705, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                    · linarith only [h0, h686, h690, h692, h704, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h634, h691, h693, h699, h701, h703, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h1, h691, h693, h702, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h0, h345, h690, h692, h701, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1, h691, h700, hlam]
                          · linarith only [h1, h690, h699, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h714 | h714
                    · linarith only [h0, h714, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h716 | h716
                      · linarith only [h0, h345, h692, h716, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
                        · linarith only [h0, h345, h692, h718, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h721 | h721
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h722 | h722
                              · linarith only [h0, h345, h692, h716, h722, hc12, hc24, hlam, hphi]
                              · linarith only [h0, h345, h722, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h1, h691, h721, hlam]
                          · linarith only [h1, h690, h691, h720, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                · linarith only [h690, h691, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h728 | h728
                · linarith only [h690, h728, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h730 | h730
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
                    · linarith only [h0, h731, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h733 | h733
                      · linarith only [h0, h686, h733, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h735 | h735
                        · linarith only [h0, h1, h690, h735, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                          · linarith only [h0, h1, h690, h731, h737, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h737, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                    · linarith only [h0, h740, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                      · linarith only [h0, h1, h690, h730, h742, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
                        · linarith only [h0, h1, h690, h730, h744, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h746 | h746
                          · linarith only [h0, h1, h690, h740, h746, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h746, hc12, hc34, hlam, hphi, ht23]

end R2N4
