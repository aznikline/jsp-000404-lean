import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3480000 in
set_option maxHeartbeats 3480000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h10, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h10, h12, h15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h14, h9, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h12, h13, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h12, h20, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h12, h23, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                                · linarith only [h0, h11, h25, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h22, h25, hc24, hlam, hphi, u4elo1]
                            · linarith only [h22, h9, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h10, h30, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                                  · linarith only [h1, h32, h37, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h34, h37, hc34, hlam, hphi, u4elo1]
                                · linarith only [h30, h34, h36, hlam]
                              · linarith only [h0, h10, h33, h35, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h34, h9, hc14, hlam, hphi, u4elo0]
                          · linarith only [h32, h33, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                          · linarith only [h0, h32, h4, h44, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                              · linarith only [h0, h32, h4, h47, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h10, h47, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h46, h9, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                            · linarith only [h55, h9, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                              · linarith only [h0, h51, h57, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h53, h57, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h0, h4, h53, h54, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h53, h7, h9, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h5, h52, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                      · linarith only [h0, h4, h51, h63, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h5, h63, h9, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h66, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h1, h71, h8, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                            · linarith only [h66, h73, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                              · linarith only [h0, h68, h75, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h70, h75, h8, hc23, hc35, hlam, hphi]
                        · linarith only [h7, h70, h8, hc13, hc35, hlam, hphi]
                      · linarith only [h5, h66, h69, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h4, h68, h80, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h5, h66, h80, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
                · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h7, h87, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                              · linarith only [h1, h7, h85, h89, h91, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                                · linarith only [h0, h86, h93, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h84, h91, h93, hc23, hlam, hphi, ht34, u4elo0]
                            · linarith only [h7, h83, h84, h87, h89, h90, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h7, h83, h85, h89, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h5, h85, h86, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h4, h7, h85, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h7, h83, h84, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                        · linarith only [h1, h104, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
                          · linarith only [h1, h106, h83, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                              · linarith only [h0, h102, h109, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                                · linarith only [h0, h103, h111, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h108, h109, h111, h2, hc23, hlam, hphi, ht34, u4elo0]
                            · linarith only [h101, h108, h7, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h102, h103, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h102, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                        · linarith only [h1, h101, h119, h7, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h119, h121, h83, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                            · linarith only [h101, h123, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                              · linarith only [h1, h117, h125, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                                · linarith only [h101, h127, hc04, hlam, hphi, u4elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                                  · linarith only [h1, h101, h117, h129, h7, hc23, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h1, h117, h129, h7, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h101, h118, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h117, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h134 | h134
              · rcases m.htr 0 3 5 (by decide) (by decide) with h135 | h135
                · linarith only [h135, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
                  · linarith only [h137, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h1, h135, h142, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                            · linarith only [h137, h144, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                              · linarith only [h0, h139, h146, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h135, h141, h146, hc23, hc35, hlam, hphi]
                        · linarith only [h134, h137, h141, h4, h6, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h137, h140, h5, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h137, h139, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h152 | h152
                · linarith only [h152, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h154 | h154
                  · linarith only [h154, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                        · linarith only [h1, h134, h154, h158, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                          · linarith only [h1, h152, h160, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                            · linarith only [h154, h162, h2, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                              · linarith only [h0, h134, h156, h164, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                                · linarith only [h0, h154, h157, h166, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h166, h4, h6, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h156, h157, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h156, h4, h6, hc12, hc25, hlam, hphi]
          · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h172 | h172
          · rcases m.htr 0 2 5 (by decide) (by decide) with h173 | h173
            · rcases m.htr 0 3 4 (by decide) (by decide) with h174 | h174
              · rcases m.htr 0 3 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                    · linarith only [h0, h172, h177, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                                · linarith only [h0, h179, h184, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h176, h183, h184, hc34, hlam, hphi, u4elo0]
                              · linarith only [h183, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h176, h182, hc14, hlam, hphi, u4elo0]
                          · linarith only [h175, h177, h179, h181, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h177, h179, h180, hc24, hlam, hphi, u4elo3]
                      · linarith only [h172, h179, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                    · linarith only [h172, h192, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                            · linarith only [h176, h197, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                                · linarith only [h176, h194, h2, h200, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                                  · linarith only [h176, h194, h199, h2, h202, hlam]
                                  · rcases h0bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h0, h194, h199, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p204_1, u1elo0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h1, h192, h194, h199, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p204_1, u1elo0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      rcases p204_3 (m.d 0 1) (by simp) with h208 | h208
                                      · rcases p204_3 (m.d 0 2) (by simp) with h209 | h209
                                        · linarith only [h0, h209, hlam]
                                        · linarith only [h172, h209, hlam]
                                      · linarith only [h2, h208, hlam]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      rcases p204_3 (m.d 0 1) (by simp) with h213 | h213
                                      · rcases p204_3 (m.d 0 2) (by simp) with h214 | h214
                                        · linarith only [h0, h214, hlam]
                                        · linarith only [h173, h214, hlam]
                                      · linarith only [h213, h3, hlam]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h0, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h4, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      rcases p204_3 (m.d 0 1) (by simp) with h221 | h221
                                      · rcases p204_3 (m.d 0 2) (by simp) with h222 | h222
                                        · rcases p204_3 (m.d 0 3) (by simp) with h223 | h223
                                          · rcases p204_3 (m.d 0 4) (by simp) with h224 | h224
                                            · linarith only [h172, h224, hlam]
                                            · rcases p204_3 (m.d 0 5) (by simp) with h226 | h226
                                              · linarith only [h173, h226, hlam]
                                              · linarith only [h176, h226, hlam]
                                          · linarith only [h174, h223, hlam]
                                        · linarith only [h172, h222, hlam]
                                      · linarith only [h2, h221, hlam]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      rcases p204_3 (m.d 0 1) (by simp) with h232 | h232
                                      · rcases p204_3 (m.d 0 2) (by simp) with h233 | h233
                                        · rcases p204_3 (m.d 0 3) (by simp) with h234 | h234
                                          · rcases p204_3 (m.d 0 4) (by simp) with h235 | h235
                                            · linarith only [h172, h235, hlam]
                                            · rcases p204_3 (m.d 0 5) (by simp) with h237 | h237
                                              · linarith only [h173, h237, hlam]
                                              · rcases h0emin with h239 | h239 | h239 | h239 | h239
                                                · rcases h3bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h192, h194, h199, hc34, hlam, hphi, ht0b, ht45, ht5b, p240_1, u0elo2]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h4, hlam, p240_1]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    rcases p240_3 (m.d 0 3) (by simp) with h244 | h244
                                                    · rcases p240_3 (m.d 1 3) (by simp) with h245 | h245
                                                      · linarith only [h1, h245, hlam]
                                                      · linarith only [h195, h245, hlam]
                                                    · linarith only [h244, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    rcases p240_3 (m.d 0 3) (by simp) with h249 | h249
                                                    · rcases p240_3 (m.d 1 3) (by simp) with h250 | h250
                                                      · linarith only [h1, h250, hlam]
                                                      · linarith only [h196, h250, hlam]
                                                    · linarith only [h249, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h1, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h192, hlam, p240_1]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p240_1, u1elo0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p240_1, u1elo0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h176, h194, h199, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p204_1, p240_1]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    rcases p240_3 (m.d 0 3) (by simp) with h260 | h260
                                                    · linarith only [h260, h4, hlam]
                                                    · linarith only [h1, h260, hlam]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h176, h194, h199, h2, h4, hlam, p204_1, p240_2]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h175, h4, hlam, p204_1, p240_2]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h174, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h195, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h199, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h202, hlam, p240_1]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h175, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h196, hlam, p240_0]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h196, h3, h4, hlam, p204_1, p240_1]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [h196, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p204_1, p240_1, u0elo1]
                                                  · have p240_0 := h240c.1
                                                    have p240_1 := h240c.2.1
                                                    have p240_2 := h240c.2.2.1
                                                    have p240_3 := h240c.2.2.2
                                                    linarith only [hlam, p240_0]
                                                · rcases h3bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h1, h192, h194, h199, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p276_1, u1elo0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h4, hlam, p276_1]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    rcases p276_3 (m.d 0 3) (by simp) with h280 | h280
                                                    · rcases p276_3 (m.d 1 3) (by simp) with h281 | h281
                                                      · linarith only [h1, h281, hlam]
                                                      · linarith only [h195, h281, hlam]
                                                    · linarith only [h280, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    rcases p276_3 (m.d 0 3) (by simp) with h285 | h285
                                                    · rcases p276_3 (m.d 1 3) (by simp) with h286 | h286
                                                      · linarith only [h1, h286, hlam]
                                                      · linarith only [h196, h286, hlam]
                                                    · linarith only [h285, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h1, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h192, hlam, p276_1]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p276_1, u1elo0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p276_1, u1elo0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h239, h4, hc23, hlam, ht01, ht12, p276_1]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    rcases p276_3 (m.d 0 3) (by simp) with h296 | h296
                                                    · linarith only [h296, h4, hlam]
                                                    · linarith only [h1, h296, hlam]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h176, h194, h199, h2, h4, hlam, p204_1, p276_2]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h175, h4, hlam, p204_1, p276_2]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h174, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h195, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h199, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h202, hlam, p276_1]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h175, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h196, hlam, p276_0]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h196, h3, h4, hlam, p204_1, p276_1]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [h196, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p204_1, p276_1, u0elo1]
                                                  · have p276_0 := h276c.1
                                                    have p276_1 := h276c.2.1
                                                    have p276_2 := h276c.2.2.1
                                                    have p276_3 := h276c.2.2.2
                                                    linarith only [hlam, p276_0]
                                                · rcases h3bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h1, h192, h194, h199, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p312_1, u1elo0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h4, hlam, p312_1]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    rcases p312_3 (m.d 0 3) (by simp) with h316 | h316
                                                    · rcases p312_3 (m.d 1 3) (by simp) with h317 | h317
                                                      · linarith only [h1, h317, hlam]
                                                      · linarith only [h195, h317, hlam]
                                                    · linarith only [h316, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    rcases p312_3 (m.d 0 3) (by simp) with h321 | h321
                                                    · rcases p312_3 (m.d 1 3) (by simp) with h322 | h322
                                                      · linarith only [h1, h322, hlam]
                                                      · linarith only [h196, h322, hlam]
                                                    · linarith only [h321, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h1, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h192, hlam, p312_1]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p312_1, u1elo0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p312_1, u1elo0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h239, hc23, hlam, ht01, ht12, p312_1]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    rcases p312_3 (m.d 0 3) (by simp) with h332 | h332
                                                    · linarith only [h332, h4, hlam]
                                                    · linarith only [h1, h332, hlam]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h176, h194, h199, h2, h4, hlam, p204_1, p312_2]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h175, h4, hlam, p204_1, p312_2]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h174, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h195, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h199, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h202, hlam, p312_1]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h175, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h196, hlam, p312_0]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h196, h3, h4, hlam, p204_1, p312_1]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [h196, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p204_1, p312_1, u0elo1]
                                                  · have p312_0 := h312c.1
                                                    have p312_1 := h312c.2.1
                                                    have p312_2 := h312c.2.2.1
                                                    have p312_3 := h312c.2.2.2
                                                    linarith only [hlam, p312_0]
                                                · linarith only [h176, h239, hlam, ht01, ht12, ht23, ht34, u4elo4]
                                                · linarith only [h239, h4, hc23, hlam, ht01, ht12, p204_1]
                                          · linarith only [h175, h234, hlam]
                                        · linarith only [h173, h233, hlam]
                                      · linarith only [h232, h3, hlam]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h1, hlam, p204_1]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h0, h1, h194, h199, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p204_1, u1elo0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      rcases p204_3 (m.d 0 1) (by simp) with h356 | h356
                                      · rcases p204_3 (m.d 0 2) (by simp) with h357 | h357
                                        · linarith only [h357, h4, hlam]
                                        · linarith only [h172, h357, hlam]
                                      · linarith only [h2, h356, hlam]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      rcases p204_3 (m.d 0 1) (by simp) with h361 | h361
                                      · rcases p204_3 (m.d 0 2) (by simp) with h362 | h362
                                        · linarith only [h362, h4, hlam]
                                        · linarith only [h173, h362, hlam]
                                      · linarith only [h3, h361, hlam]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h2, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h172, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h174, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h176, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h3, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h173, hlam, p204_1]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h175, hlam, p204_0]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [h176, h194, h199, h2, hc34, hlam, hphi, p204_1, u4elo4]
                                    · have p204_0 := h204c.1
                                      have p204_1 := h204c.2.1
                                      have p204_2 := h204c.2.2.1
                                      have p204_3 := h204c.2.2.2
                                      linarith only [hlam, p204_0]
                              · linarith only [h199, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h1, h175, h192, h194, h196, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h192, h194, h195, hc24, hlam, hphi, u4elo3]
                      · linarith only [h172, h194, h4, hc12, hc23, hlam, hphi]
                · linarith only [h173, h175, h4, hlam]
              · linarith only [h172, h174, h4, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h382 | h382
              · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
                · rcases m.htr 0 4 5 (by decide) (by decide) with h384 | h384
                  · linarith only [h172, h173, h384, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                    · linarith only [h172, h386, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h391 | h391
                            · linarith only [h384, h391, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h394 | h394
                                · linarith only [h0, h384, h388, h394, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h0, h173, h388, h393, h394, hc34, hlam, hphi, u4elo4]
                              · linarith only [h0, h388, h393, h4, hc24, hlam, hphi, u4elo3]
                          · linarith only [h1, h383, h386, h388, h390, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h386, h388, h389, hc24, hlam, hphi, u4elo3]
                      · linarith only [h172, h173, h388, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h401 | h401
                  · linarith only [h172, h383, h4, h401, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
                    · linarith only [h172, h4, h403, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                          · linarith only [h0, h383, h4, h405, h407, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h409 | h409
                            · linarith only [h401, h409, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                                · linarith only [h0, h401, h405, h412, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h0, h173, h405, h412, hc24, hlam, hphi, u4elo4]
                              · linarith only [h0, h4, h405, h411, hc24, hlam, hphi, u4elo3]
                        · linarith only [h382, h383, h401, h406, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h172, h4, h405, hc12, hc23, hlam, hphi]
              · linarith only [h172, h382, h4, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h419 | h419
            · rcases m.htr 0 3 4 (by decide) (by decide) with h420 | h420
              · rcases m.htr 0 3 5 (by decide) (by decide) with h421 | h421
                · rcases m.htr 0 4 5 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                    · linarith only [h0, h172, h423, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
                      · linarith only [h172, h419, h423, h425, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h429 | h429
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h431 | h431
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h432 | h432
                                  · linarith only [h1, h427, h432, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h422, h432, hc34, hlam, hphi, u4elo0]
                                · linarith only [h172, h429, h431, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · linarith only [h4, h419, h430, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h422, h429, hc14, hlam, hphi, u4elo0]
                          · linarith only [h421, h427, h428, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                          · linarith only [h1, h420, h427, h439, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h172, h419, h421, h423, h439, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h172, h419, h422, hlam]
                · linarith only [h4, h419, h421, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h444 | h444
                · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                    · linarith only [h4, h419, h446, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                      · linarith only [h0, h4, h420, h448, hc24, hlam, hphi, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                        · linarith only [h1, h420, h450, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h455 | h455
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h456 | h456
                                  · rcases h0bigk with h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h419, h455, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h4, h419, h455, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h4, h419, h420, h455, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      rcases p457_3 (m.d 0 1) (by simp) with h462 | h462
                                      · rcases p457_3 (m.d 0 2) (by simp) with h463 | h463
                                        · linarith only [h0, h463, hlam]
                                        · linarith only [h419, h463, hlam]
                                      · linarith only [h3, h462, hlam]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h0, hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h4, hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h172, hlam, p457_1]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h4, h420, h454, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p457_1, u4elo2]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h1, hlam, p457_1]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h420, h454, hc02, hlam, hphi, ht23, ht34, p457_1, u4elo2]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h420, hlam, p457_1]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h419, h420, h454, h455, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p457_1, u4elo2]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h2, hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h419, h455, hc45, hlam, hphi, ht0b, ht5b, p457_1, u0elo3]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h420, h454, hc03, hlam, hphi, ht34, p457_1, u4elo2]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      rcases p457_3 (m.d 0 1) (by simp) with h481 | h481
                                      · rcases p457_3 (m.d 0 2) (by simp) with h482 | h482
                                        · linarith only [h172, h482, hlam]
                                        · linarith only [h419, h482, hlam]
                                      · linarith only [h3, h481, hlam]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h3, hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h419, hlam, p457_1]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h444, hlam, p457_0]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [h445, hlam, p457_1]
                                    · have p457_0 := h457c.1
                                      have p457_1 := h457c.2.1
                                      have p457_2 := h457c.2.2.1
                                      have p457_3 := h457c.2.2.2
                                      linarith only [hlam, p457_0]
                                  · linarith only [h172, h2, h419, h420, h455, h456, hc14, hlam, hphi, u4elo2]
                                · linarith only [h172, h419, h455, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                              · linarith only [h4, h419, h454, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h445, h450, h452, h453, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h420, h444, h446, h452, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h4, h419, h420, h445, hlam]
                · linarith only [h4, h419, h444, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h498 | h498
              · rcases m.htr 0 3 5 (by decide) (by decide) with h499 | h499
                · rcases m.htr 0 4 5 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
                    · linarith only [h0, h4, h501, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h503 | h503
                      · linarith only [h0, h172, h503, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h507 | h507
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                                  · linarith only [h1, h505, h510, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h507, h510, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1, h505, h507, h509, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h4, h508, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h500, h507, hc14, hlam, hphi, u4elo0]
                          · linarith only [h499, h505, h506, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h517 | h517
                          · linarith only [h498, h505, h517, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h519 | h519
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                                  · rcases h0bigk with h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      rcases p523_3 (m.d 0 1) (by simp) with h525 | h525
                                      · rcases p523_3 (m.d 0 2) (by simp) with h526 | h526
                                        · linarith only [h0, h526, hlam]
                                        · rcases p523_3 (m.d 0 3) (by simp) with h528 | h528
                                          · linarith only [h1, h528, hlam]
                                          · linarith only [h4, h528, hlam]
                                      · linarith only [h0, h525, hlam]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h498, h501, h517, h522, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p523_1, u1elo0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h2, h519, hc45, hlam, hphi, ht01, ht0b, ht5b, p523_1, u1elo0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h499, h501, h517, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p523_1, u1elo0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h0, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h4, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h172, hlam, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h419, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h1, hlam, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      rcases p523_3 (m.d 0 1) (by simp) with h541 | h541
                                      · rcases p523_3 (m.d 0 2) (by simp) with h542 | h542
                                        · linarith only [h4, h542, hlam]
                                        · rcases p523_3 (m.d 0 3) (by simp) with h544 | h544
                                          · rcases p523_3 (m.d 0 4) (by simp) with h545 | h545
                                            · linarith only [h498, h545, hlam]
                                            · linarith only [h172, h545, hlam]
                                          · linarith only [h4, h544, hlam]
                                      · linarith only [h0, h541, hlam]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h498, h501, h517, h522, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p523_1, u0elo2]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h1, h499, h501, h517, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p523_1, u1elo0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h2, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hc02, hlam, hphi, ht23, ht34, p523_1, u4elo0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h498, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h172, h499, h501, h517, hc12, hlam, hphi, ht23, ht34, p523_1, u4elo2]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h3, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h0, h419, h521, hc12, hlam, hphi, ht23, ht34, p523_1, u4elo2]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h499, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h500, hlam, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                  · linarith only [h519, h522, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1, h172, h498, h505, h519, h521, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h4, h498, h520, hlam]
                            · linarith only [h500, h519, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h567 | h567
                    · linarith only [h0, h4, h499, h567, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h569 | h569
                      · linarith only [h0, h172, h500, h569, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h573 | h573
                            · linarith only [h172, h500, h573, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h576 | h576
                                · linarith only [h0, h172, h500, h576, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h172, h576, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h571, h575, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h1, h499, h571, h572, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h498, h500, h571, hc13, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h582 | h582
                  · linarith only [h498, h499, h582, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                    · linarith only [h0, h4, h584, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                      · linarith only [h0, h172, h586, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h589 | h589
                          · linarith only [h1, h499, h589, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h591 | h591
                            · linarith only [h2, h582, h591, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                                · linarith only [h172, h582, h594, hc02, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h172, h594, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h1, h4, h588, h593, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h498, h499, h582, h588, hc13, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
                · rcases m.htr 0 4 5 (by decide) (by decide) with h600 | h600
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                    · linarith only [h0, h172, h601, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
                      · linarith only [h0, h419, h498, h599, h603, hc24, hlam, hphi, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                        · linarith only [h1, h498, h605, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h607 | h607
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h608 | h608
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h609 | h609
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h611 | h611
                                  · rcases h0bigk with h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      rcases p612_3 (m.d 0 1) (by simp) with h614 | h614
                                      · rcases p612_3 (m.d 0 2) (by simp) with h615 | h615
                                        · linarith only [h0, h615, hlam]
                                        · rcases p612_3 (m.d 0 3) (by simp) with h617 | h617
                                          · linarith only [h1, h617, hlam]
                                          · linarith only [h4, h617, hlam]
                                      · linarith only [h0, h614, hlam]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h1, h607, h611, hc45, hlam, hphi, ht01, ht0b, ht5b, p612_1, u1elo0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h1, h498, h607, h611, hc45, hlam, hphi, ht01, ht0b, ht5b, p612_1, u1elo0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      rcases p612_3 (m.d 0 1) (by simp) with h623 | h623
                                      · rcases p612_3 (m.d 0 2) (by simp) with h624 | h624
                                        · linarith only [h0, h624, hlam]
                                        · rcases p612_3 (m.d 0 3) (by simp) with h626 | h626
                                          · linarith only [h1, h626, hlam]
                                          · linarith only [h599, h626, hlam]
                                      · linarith only [h3, h623, hlam]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h0, hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h4, hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h172, hlam, p612_1]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h419, hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h1, hlam, p612_1]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h498, h609, hc02, hlam, hphi, ht23, ht34, p612_1, u4elo2]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h498, hlam, p612_1]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h498, h609, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p612_1, u4elo2]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h2, hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, p612_1, u4elo0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h498, h609, hc03, hlam, hphi, ht34, p612_1, u4elo2]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h0, h419, h498, h609, hc12, hlam, hphi, ht23, ht34, p612_1, u4elo2]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h3, hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h0, h498, h599, h609, hc12, hlam, hphi, ht23, ht34, p612_1, u4elo2]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h599, hlam, p612_0]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [h600, hlam, p612_1]
                                    · have p612_0 := h612c.1
                                      have p612_1 := h612c.2.1
                                      have p612_2 := h612c.2.2.1
                                      have p612_3 := h612c.2.2.2
                                      linarith only [hlam, p612_0]
                                  · linarith only [h498, h611, hc03, hlam, hphi, ht34, u4elo4]
                                · linarith only [h2, h608, h610, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h4, h609, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h172, h600, h608, hc14, hlam, hphi, u4elo2]
                          · linarith only [h498, h599, h607, hc13, hlam, hphi, ht34, u4elo3]
                  · linarith only [h498, h599, h600, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h656 | h656
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
                    · linarith only [h0, h4, h657, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h659 | h659
                      · linarith only [h0, h172, h659, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
                        · linarith only [h1, h4, h498, h661, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h663 | h663
                          · linarith only [h0, h4, h599, h661, h663, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h665 | h665
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h666 | h666
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h667 | h667
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                                  · rcases h0bigk with h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      rcases p669_3 (m.d 0 1) (by simp) with h671 | h671
                                      · rcases p669_3 (m.d 0 2) (by simp) with h672 | h672
                                        · linarith only [h0, h672, hlam]
                                        · rcases p669_3 (m.d 0 3) (by simp) with h674 | h674
                                          · linarith only [h1, h674, hlam]
                                          · linarith only [h4, h674, hlam]
                                      · linarith only [h0, h671, hlam]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      rcases p669_3 (m.d 0 1) (by simp) with h678 | h678
                                      · rcases p669_3 (m.d 0 2) (by simp) with h679 | h679
                                        · linarith only [h0, h679, hlam]
                                        · rcases p669_3 (m.d 0 3) (by simp) with h681 | h681
                                          · linarith only [h1, h681, hlam]
                                          · rcases p669_3 (m.d 0 4) (by simp) with h683 | h683
                                            · linarith only [h2, h683, hlam]
                                            · linarith only [h498, h683, hlam]
                                      · linarith only [h1, h678, hlam]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h2, h665, hc45, hlam, hphi, ht01, ht0b, ht5b, p669_1, u1elo0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      rcases p669_3 (m.d 0 1) (by simp) with h688 | h688
                                      · rcases p669_3 (m.d 0 2) (by simp) with h689 | h689
                                        · linarith only [h0, h689, hlam]
                                        · rcases p669_3 (m.d 0 3) (by simp) with h691 | h691
                                          · linarith only [h1, h691, hlam]
                                          · rcases p669_3 (m.d 0 4) (by simp) with h693 | h693
                                            · linarith only [h2, h693, hlam]
                                            · linarith only [h656, h693, hlam]
                                      · linarith only [h3, h688, hlam]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h0, hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h4, hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h172, hlam, p669_1]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h419, hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h1, hlam, p669_1]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h0, h599, h666, h668, hc12, hc23, hlam, hphi, p669_1]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h498, hlam, p669_1]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h599, hlam, p669_1]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h2, hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, p669_1, u4elo0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h498, h666, hc03, hlam, hphi, ht34, p669_1, u4elo2]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h0, h4, h498, h599, h666, hc12, hlam, hphi, ht23, ht34, p669_1, u4elo2]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h3, hlam, p669_0]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h0, h599, h666, h668, hc12, hlam, hphi, ht23, ht34, p669_1, u4elo2]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h0, h4, h599, h666, h668, hc12, hlam, hphi, ht23, ht34, p669_1, u4elo2]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [h656, hlam, p669_1]
                                    · have p669_0 := h669c.1
                                      have p669_1 := h669c.2.1
                                      have p669_2 := h669c.2.2.1
                                      have p669_3 := h669c.2.2.2
                                      linarith only [hlam, p669_0]
                                  · linarith only [h498, h665, h668, hc04, hlam, hphi, u4elo1]
                                · linarith only [h2, h665, h667, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h4, h666, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h172, h656, h665, hc14, hlam, hphi, u4elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                    · linarith only [h0, h4, h721, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                      · linarith only [h0, h172, h723, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
                        · linarith only [h1, h498, h656, h725, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h727 | h727
                          · linarith only [h0, h4, h599, h725, h727, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h729 | h729
                            · linarith only [h2, h656, h729, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h731 | h731
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h732 | h732
                                · linarith only [h0, h4, h498, h656, h732, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h172, h732, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h4, h731, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h736 | h736
        · rcases m.htr 0 2 4 (by decide) (by decide) with h737 | h737
          · rcases m.htr 0 2 5 (by decide) (by decide) with h738 | h738
            · linarith only [h0, h3, h738, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h740 | h740
              · rcases m.htr 0 3 5 (by decide) (by decide) with h741 | h741
                · linarith only [h1, h3, h741, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h743 | h743
                  · linarith only [h2, h3, h743, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
                    · linarith only [h0, h3, h745, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h0, h3, h736, h745, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h748 | h748
                · linarith only [h1, h3, h748, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                  · linarith only [h0, h3, h737, h750, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
                    · linarith only [h0, h3, h752, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h0, h3, h736, h752, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · linarith only [h736, h737, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h756 | h756
          · rcases m.htr 0 2 5 (by decide) (by decide) with h757 | h757
            · linarith only [h0, h3, h757, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h759 | h759
              · rcases m.htr 0 3 5 (by decide) (by decide) with h760 | h760
                · linarith only [h1, h3, h760, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h762 | h762
                  · linarith only [h2, h3, h762, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
                    · linarith only [h0, h3, h736, h764, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
                      · linarith only [h0, h3, h766, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · linarith only [h736, h756, h766, hc12, hc23, hlam, hphi]
              · linarith only [h736, h756, h759, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h770 | h770
            · linarith only [h0, h3, h756, h770, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h772 | h772
              · rcases m.htr 0 3 5 (by decide) (by decide) with h773 | h773
                · linarith only [h1, h3, h773, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h775 | h775
                  · linarith only [h2, h3, h775, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
                    · linarith only [h0, h736, h777, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
                      · linarith only [h0, h3, h779, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h781 | h781
                        · linarith only [h1, h3, h781, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h1, h3, h772, h777, h781, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h784 | h784
                · linarith only [h1, h3, h784, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h786 | h786
                  · linarith only [h2, h3, h786, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                    · linarith only [h0, h736, h788, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h790 | h790
                      · linarith only [h0, h756, h790, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h792 | h792
                        · linarith only [h1, h772, h786, h792, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
                          · linarith only [h784, h792, h794, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
                            · linarith only [h2, h3, h786, h796, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · linarith only [h0, h3, h796, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h800 | h800
    · rcases m.htr 0 1 5 (by decide) (by decide) with h801 | h801
      · rcases m.htr 0 2 3 (by decide) (by decide) with h802 | h802
        · linarith only [h0, h1, h802, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h804 | h804
          · rcases m.htr 0 2 5 (by decide) (by decide) with h805 | h805
            · rcases m.htr 0 3 4 (by decide) (by decide) with h806 | h806
              · rcases m.htr 0 3 5 (by decide) (by decide) with h807 | h807
                · rcases m.htr 0 4 5 (by decide) (by decide) with h808 | h808
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h809 | h809
                    · linarith only [h0, h802, h809, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h811 | h811
                      · linarith only [h0, h1, h811, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h804, h811, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                    · linarith only [h0, h1, h814, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
                      · linarith only [h0, h1, h816, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h804, h816, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h1, h801, h807, hlam]
              · linarith only [h0, h1, h806, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h821 | h821
              · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
                · rcases m.htr 0 4 5 (by decide) (by decide) with h823 | h823
                  · linarith only [h804, h805, h823, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                    · linarith only [h0, h802, h804, h825, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h827 | h827
                      · linarith only [h0, h1, h827, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h804, h805, h827, hc12, hc25, hlam, hphi]
                · linarith only [h1, h801, h822, hlam]
              · linarith only [h1, h801, h804, h805, h821, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h832 | h832
            · rcases m.htr 0 3 4 (by decide) (by decide) with h833 | h833
              · rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
                · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
                    · linarith only [h0, h802, h836, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                      · linarith only [h0, h1, h838, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h842 | h842
                            · linarith only [h1, h800, h842, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · linarith only [h835, h838, h842, hc12, hlam, hphi, ht23, ht34, u4elo0]
                          · linarith only [h1, h800, h838, h841, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h800, h838, h840, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h804, h832, h835, hlam]
                · linarith only [h1, h800, h804, h832, h834, hc14, hlam, hphi, u4elo2]
              · linarith only [h1, h800, h833, hc14, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h850 | h850
              · rcases m.htr 0 3 5 (by decide) (by decide) with h851 | h851
                · rcases m.htr 0 4 5 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
                    · linarith only [h0, h802, h853, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h855 | h855
                      · linarith only [h0, h804, h855, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h857 | h857
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h858 | h858
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h859 | h859
                            · linarith only [h1, h800, h859, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                            · linarith only [h852, h855, h859, hc12, hlam, hphi, ht23, ht34, u4elo0]
                          · linarith only [h1, h800, h855, h858, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h800, h855, h857, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h864 | h864
                    · linarith only [h0, h804, h864, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
                      · linarith only [h0, h1, h804, h866, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h868 | h868
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h869 | h869
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h870 | h870
                            · linarith only [h800, h852, h870, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h872 | h872
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h873 | h873
                                · linarith only [h0, h804, h852, h873, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h0, h804, h873, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h864, h868, h872, hc01, hlam, hphi, u1elo3]
                          · linarith only [h1, h800, h851, h866, h869, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h800, h866, h868, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h801, h851, hlam]
              · linarith only [h1, h800, h850, hc14, hlam, hphi, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h881 | h881
        · linarith only [h0, h1, h881, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h883 | h883
          · rcases m.htr 0 2 5 (by decide) (by decide) with h884 | h884
            · linarith only [h0, h801, h884, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h886 | h886
              · rcases m.htr 0 3 5 (by decide) (by decide) with h887 | h887
                · rcases m.htr 0 4 5 (by decide) (by decide) with h888 | h888
                  · linarith only [h800, h801, h888, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h890 | h890
                    · linarith only [h0, h881, h890, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h892 | h892
                      · linarith only [h0, h1, h892, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h883, h884, h892, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h895 | h895
                  · linarith only [h1, h800, h887, h895, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
                    · linarith only [h881, h883, h897, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
                      · linarith only [h0, h1, h899, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h883, h884, h899, hc12, hc25, hlam, hphi]
              · linarith only [h0, h1, h886, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h903 | h903
            · linarith only [h0, h801, h883, h903, hc12, hlam, hphi, ht23, ht34, u4elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h905 | h905
              · rcases m.htr 0 3 5 (by decide) (by decide) with h906 | h906
                · rcases m.htr 0 4 5 (by decide) (by decide) with h907 | h907
                  · linarith only [h800, h801, h907, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h909 | h909
                    · linarith only [h0, h1, h909, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h911 | h911
                      · linarith only [h0, h1, h911, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h913 | h913
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h914 | h914
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h915 | h915
                            · linarith only [h800, h801, h907, h915, hlam]
                            · linarith only [h800, h801, h911, h915, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1, h906, h914, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h800, h911, h913, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
                  · linarith only [h800, h801, h920, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
                    · linarith only [h0, h881, h922, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h924 | h924
                      · linarith only [h0, h1, h924, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h926 | h926
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h927 | h927
                          · linarith only [h1, h906, h927, hc01, hlam, hphi, u1elo2]
                          · linarith only [h1, h800, h924, h927, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h800, h924, h926, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h800, h905, hc14, hlam, hphi, u4elo3]
    · linarith only [h0, h800, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
