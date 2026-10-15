import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_R_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h3bigk := hb3.1
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
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h10, h20, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h10, h20, h23, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h10, h23, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h10, h22, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h29, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h27, h29, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h27, h28, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h0, h27, h33, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h33, h5, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h36, h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h0, h40, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h38, h40, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h38, h39, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h38, h4, h8, hc35, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h45 | h45
                  · linarith only [h45, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                          · linarith only [h0, h50, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h48, h50, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h48, h49, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h48, h7, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                          · linarith only [h0, h57, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                          · linarith only [h55, h57, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h55, h56, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h47, h55, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
            · linarith only [h4, h64, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h66 | h66
              · linarith only [h4, h66, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h4, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                        · linarith only [h0, h64, h70, h73, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                          · linarith only [h0, h66, h75, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                            · linarith only [h1, h77, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h4, h69, h71, h77, hc23, hlam, hphi, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h64, h80, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                        · linarith only [h0, h64, h82, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h0, h66, h84, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                            · linarith only [h1, h86, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h4, h69, h80, h86, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h68, h69, h89, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                      · linarith only [h0, h4, h91, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
                        · linarith only [h0, h4, h93, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                          · linarith only [h0, h66, h95, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
                            · linarith only [h1, h68, h69, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                                · linarith only [h100, h64, h68, h69, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h0, h100, h4, hc35, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h0, h4, h99, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h68, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                      · linarith only [h0, h107, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h106, h109, h64, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h0, h111, h66, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                            · linarith only [h1, h104, h113, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                              · linarith only [h106, h115, h68, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h0, h115, h4, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                      · linarith only [h0, h118, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                        · linarith only [h0, h120, h64, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                          · linarith only [h0, h122, h66, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                            · linarith only [h1, h104, h124, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                              · linarith only [h0, h126, h4, h68, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h126, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h129 | h129
          · rcases m.htr 0 2 4 (by decide) (by decide) with h130 | h130
            · rcases m.htr 0 2 5 (by decide) (by decide) with h131 | h131
              · linarith only [h0, h131, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h129, h131, hc25, hlam, hphi, u2ehi2]
            · linarith only [h129, h130, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h135 | h135
            · linarith only [h129, h135, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h137 | h137
              · linarith only [h129, h137, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
                · rcases m.htr 0 3 5 (by decide) (by decide) with h140 | h140
                  · linarith only [h1, h140, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h142 | h142
                    · linarith only [h139, h140, h142, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                      · linarith only [h0, h144, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                        · linarith only [h1, h135, h144, h146, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h0, h129, h137, h148, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · linarith only [h1, h144, h148, h3, hc25, hlam, hphi, u2ehi1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
                  · linarith only [h139, h151, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                    · linarith only [h153, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                      · linarith only [h0, h135, h155, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                        · linarith only [h1, h135, h155, h157, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                          · linarith only [h0, h129, h137, h159, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · linarith only [h1, h155, h159, h3, hc25, hlam, hphi, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h162 | h162
        · linarith only [h162, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h164 | h164
          · rcases m.htr 0 2 4 (by decide) (by decide) with h165 | h165
            · linarith only [h0, h165, h2, hlam]
            · linarith only [h164, h165, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h168 | h168
            · linarith only [h164, h168, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h170 | h170
              · linarith only [h1, h164, h170, h2, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
                · linarith only [h1, h172, h2, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h172, h174, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                      · linarith only [h0, h164, h177, h2, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                        · linarith only [h0, h168, h176, h179, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h1, h177, h179, h2, hc24, hlam, hphi, u2ehi1]
                    · linarith only [h0, h176, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h183 | h183
      · rcases m.htr 0 1 5 (by decide) (by decide) with h184 | h184
        · linarith only [h1, h184, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h186 | h186
          · linarith only [h0, h1, h186, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h188 | h188
            · linarith only [h186, h188, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h190 | h190
              · linarith only [h186, h190, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
                · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h1, h183, h194, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
                      · linarith only [h0, h1, h196, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h1, h196, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h193, hc35, hlam, hphi, ht23, u2ehi1]
                · linarith only [h0, h1, h192, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h201 | h201
        · linarith only [h1, h201, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h203 | h203
          · linarith only [h0, h1, h203, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h205 | h205
            · linarith only [h203, h205, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
              · linarith only [h0, h1, h207, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h209 | h209
                · rcases m.htr 0 3 5 (by decide) (by decide) with h210 | h210
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
                      · linarith only [h0, h1, h203, h212, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h1, h212, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h183, h211, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h0, h183, h209, h210, hc35, hlam, hphi, ht23, u2ehi1]
                · linarith only [h0, h1, h209, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h218 | h218
    · rcases m.htr 0 1 4 (by decide) (by decide) with h219 | h219
      · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
        · linarith only [h0, h220, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h222 | h222
          · rcases m.htr 0 2 4 (by decide) (by decide) with h223 | h223
            · rcases m.htr 0 2 5 (by decide) (by decide) with h224 | h224
              · rcases m.htr 0 3 4 (by decide) (by decide) with h225 | h225
                · rcases m.htr 0 3 5 (by decide) (by decide) with h226 | h226
                  · linarith only [h0, h218, h226, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
                    · linarith only [h225, h226, h228, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h233 | h233
                            · linarith only [h218, h220, h226, h232, h233, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h218, h220, h230, h233, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h0, h218, h224, h230, h232, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h218, h230, h231, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h224, h230, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h239 | h239
                  · linarith only [h219, h220, h225, h239, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h219, h220, h241, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                            · linarith only [h218, h220, h239, h245, h246, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h218, h220, h243, h246, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h0, h218, h224, h245, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h224, h244, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h224, h243, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h222, h224, hc25, hlam, hphi, u2ehi2]
            · linarith only [h222, h223, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h218, h222, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h255 | h255
        · linarith only [h0, h255, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h257 | h257
          · rcases m.htr 0 2 4 (by decide) (by decide) with h258 | h258
            · rcases m.htr 0 2 5 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
                · linarith only [h218, h219, h260, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h260, h262, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h268 | h268
                            · linarith only [h218, h219, h262, h266, h268, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h218, h255, h265, h268, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h218, h219, h265, h266, h267, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h218, h258, h265, h266, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h259, h265, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                      · linarith only [h218, h219, h264, h274, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h259, h274, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h258, h259, hc25, hlam, hphi, u2ehi3]
            · linarith only [h257, h258, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h218, h257, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h280 | h280
      · rcases m.htr 0 1 5 (by decide) (by decide) with h281 | h281
        · linarith only [h0, h281, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h283 | h283
          · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
            · rcases m.htr 0 2 5 (by decide) (by decide) with h285 | h285
              · rcases m.htr 0 3 4 (by decide) (by decide) with h286 | h286
                · rcases m.htr 0 3 5 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h0, h280, h288, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h292 | h292
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h295 | h295
                                · linarith only [h0, h283, h295, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h297 | h297
                                  · linarith only [h287, h288, h294, h295, h297, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                                    · linarith only [h218, h287, h288, h290, h294, h295, h299, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                    · rcases h0bigk with h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h0, hlam, p301_1]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h218, hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h280, h281, h288, h291, hc45, hlam, hphi, ht23, ht34, p301_1, u2ehi3]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h281, hlam, p301_1]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h0, h280, h291, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p301_1, u2ehi3]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h0, h218, h280, h291, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p301_1, u2ehi3]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        rcases p301_3 (m.d 0 1) (by simp) with h310 | h310
                                        · linarith only [h0, h310, hlam]
                                        · linarith only [h280, h310, hlam]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p301_1, u5ehi0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h218, h280, h290, h291, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p301_1, u2ehi3]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h283, hlam, p301_1]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        rcases p301_3 (m.d 0 1) (by simp) with h317 | h317
                                        · linarith only [h218, h317, hlam]
                                        · linarith only [h280, h317, hlam]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h218, h290, hc12, hlam, hphi, ht01, ht0b, ht5b, p301_1, u5ehi0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h280, hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h284, hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h286, hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h288, hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h280, h291, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p301_1, u2ehi3]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h285, hlam, p301_1]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h287, hlam, p301_0]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [h280, h288, h291, hc45, hlam, hphi, ht23, ht34, p301_1, u2ehi3]
                                      · have p301_0 := h301c.1
                                        have p301_1 := h301c.2.1
                                        have p301_2 := h301c.2.2.1
                                        have p301_3 := h301c.2.2.2
                                        linarith only [hlam, p301_0]
                              · linarith only [h286, h288, h294, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h218, h280, h291, h293, hc35, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h0, h280, h291, h292, hc25, hlam, hphi, u2ehi3]
                        · linarith only [h0, h285, h291, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h283, h287, h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h336 | h336
                    · linarith only [h218, h280, h336, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                        · linarith only [h218, h280, h287, h339, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h285, h339, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h283, h338, hlam]
                · linarith only [h218, h280, h286, hlam]
              · linarith only [h283, h285, hc25, hlam, hphi, u2ehi2]
            · linarith only [h283, h284, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h346 | h346
            · linarith only [h283, h346, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h280, h346, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h349 | h349
        · linarith only [h0, h349, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h351 | h351
          · rcases m.htr 0 2 4 (by decide) (by decide) with h352 | h352
            · rcases m.htr 0 2 5 (by decide) (by decide) with h353 | h353
              · rcases m.htr 0 3 4 (by decide) (by decide) with h354 | h354
                · rcases m.htr 0 3 5 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h361 | h361
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                                · linarith only [h351, h362, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h364 | h364
                                  · linarith only [h218, h355, h357, h361, h362, h364, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                                    · linarith only [h218, h355, h357, h361, h362, h364, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h0, hlam, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h218, hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h280, hlam, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h349, hlam, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        rcases p368_3 (m.d 0 1) (by simp) with h374 | h374
                                        · linarith only [h0, h374, hlam]
                                        · rcases p368_3 (m.d 0 2) (by simp) with h376 | h376
                                          · rcases p368_3 (m.d 0 3) (by simp) with h377 | h377
                                            · linarith only [h351, h377, hlam]
                                            · linarith only [h218, h377, hlam]
                                          · linarith only [h0, h376, hlam]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h0, h354, h356, h362, h366, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h0, h356, h362, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p368_1, u5ehi0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        rcases p368_3 (m.d 0 1) (by simp) with h385 | h385
                                        · linarith only [h218, h385, hlam]
                                        · rcases p368_3 (m.d 0 2) (by simp) with h387 | h387
                                          · rcases p368_3 (m.d 0 3) (by simp) with h388 | h388
                                            · rcases p368_3 (m.d 0 4) (by simp) with h389 | h389
                                              · linarith only [h354, h389, hlam]
                                              · linarith only [h280, h389, hlam]
                                            · linarith only [h218, h388, hlam]
                                          · linarith only [h0, h387, hlam]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h351, hlam, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h218, h356, h357, h361, h362, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi3]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h218, h356, h357, h361, h362, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi3]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        rcases p368_3 (m.d 0 1) (by simp) with h398 | h398
                                        · linarith only [h280, h398, hlam]
                                        · rcases p368_3 (m.d 0 2) (by simp) with h400 | h400
                                          · rcases p368_3 (m.d 0 3) (by simp) with h401 | h401
                                            · rcases p368_3 (m.d 0 4) (by simp) with h402 | h402
                                              · rcases p368_3 (m.d 0 5) (by simp) with h403 | h403
                                                · linarith only [h356, h403, hlam]
                                                · linarith only [h349, h403, hlam]
                                              · linarith only [h280, h402, hlam]
                                            · linarith only [h218, h401, hlam]
                                          · linarith only [h0, h400, hlam]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h352, hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h354, hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h356, h361, h362, h366, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi3]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        rcases p368_3 (m.d 0 1) (by simp) with h413 | h413
                                        · linarith only [h349, h413, hlam]
                                        · rcases p368_3 (m.d 0 2) (by simp) with h415 | h415
                                          · rcases p368_3 (m.d 0 3) (by simp) with h416 | h416
                                            · rcases p368_3 (m.d 0 4) (by simp) with h417 | h417
                                              · rcases p368_3 (m.d 0 5) (by simp) with h418 | h418
                                                · rcases h3bigk with h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h218, hlam, p419_1]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    rcases p419_3 (m.d 0 3) (by simp) with h422 | h422
                                                    · rcases p419_3 (m.d 1 3) (by simp) with h423 | h423
                                                      · rcases p419_3 (m.d 2 3) (by simp) with h424 | h424
                                                        · linarith only [h351, h424, hlam]
                                                        · rcases p419_3 (m.d 3 4) (by simp) with h426 | h426
                                                          · linarith only [h354, h426, hlam]
                                                          · rcases p419_3 (m.d 3 5) (by simp) with h428 | h428
                                                            · linarith only [h355, h428, hlam]
                                                            · linarith only [h362, h428, hlam]
                                                      · linarith only [h357, h423, hlam]
                                                    · linarith only [h351, h422, hlam]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h355, h361, h362, hlam, p419_2]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h361, h362, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h355, h357, h361, h362, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    rcases p419_3 (m.d 0 3) (by simp) with h437 | h437
                                                    · linarith only [h218, h437, hlam]
                                                    · linarith only [h351, h437, hlam]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h218, h354, h356, h361, h362, h366, hlam, p419_2]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h361, h362, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h351, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h357, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h354, h356, h362, h366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p419_1]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h362, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h354, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h360, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p419_1, u5ehi1]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h361, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h366, hlam, p419_1]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h355, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h360, hlam, p419_0]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [h0, h351, h354, h356, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi2]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    rcases p419_3 (m.d 0 3) (by simp) with h455 | h455
                                                    · rcases p419_3 (m.d 1 3) (by simp) with h456 | h456
                                                      · rcases p419_3 (m.d 2 3) (by simp) with h457 | h457
                                                        · linarith only [h362, h457, hlam]
                                                        · linarith only [h361, h457, hlam]
                                                      · linarith only [h218, h354, h356, h361, h366, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                                    · linarith only [h354, h455, hlam]
                                                  · have p419_0 := h419c.1
                                                    have p419_1 := h419c.2.1
                                                    have p419_2 := h419c.2.2.1
                                                    have p419_3 := h419c.2.2.2
                                                    linarith only [hlam, p419_0]
                                                · linarith only [h349, h418, hlam]
                                              · linarith only [h280, h417, hlam]
                                            · linarith only [h218, h416, hlam]
                                          · linarith only [h0, h415, hlam]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h353, hlam, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h355, hlam, p368_0]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [h356, hlam, p368_1]
                                      · have p368_0 := h368c.1
                                        have p368_1 := h368c.2.1
                                        have p368_2 := h368c.2.2.1
                                        have p368_3 := h368c.2.2.2
                                        linarith only [hlam, p368_0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h471 | h471
                                · linarith only [h354, h361, h471, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h473 | h473
                                  · linarith only [h0, h352, h473, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h475 | h475
                                    · linarith only [h0, h351, h354, h361, h473, h475, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h356, h361, h475, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h218, h354, h356, h360, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h280, h356, h358, h359, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h0, h351, h354, h356, h358, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h351, h354, h356, h357, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h487 | h487
                                · linarith only [h351, h487, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                                  · linarith only [h0, h351, h355, h356, h486, h487, h489, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h491 | h491
                                    · linarith only [h0, h351, h354, h356, h491, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                    · rcases h0bigk with h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h0, hlam, p493_1]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h218, hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h280, hlam, p493_1]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h349, hlam, p493_1]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        rcases p493_3 (m.d 0 1) (by simp) with h499 | h499
                                        · linarith only [h0, h499, hlam]
                                        · rcases p493_3 (m.d 0 2) (by simp) with h501 | h501
                                          · rcases p493_3 (m.d 0 3) (by simp) with h502 | h502
                                            · linarith only [h351, h502, hlam]
                                            · linarith only [h218, h502, hlam]
                                          · linarith only [h0, h501, hlam]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h0, h355, h486, h487, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p493_1, u2ehi3]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        rcases p493_3 (m.d 0 1) (by simp) with h508 | h508
                                        · linarith only [h0, h508, hlam]
                                        · rcases p493_3 (m.d 0 2) (by simp) with h510 | h510
                                          · rcases p493_3 (m.d 0 3) (by simp) with h511 | h511
                                            · linarith only [h351, h511, hlam]
                                            · linarith only [h354, h511, hlam]
                                          · linarith only [h352, h510, hlam]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h0, h355, h486, h487, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p493_1, u2ehi3]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        rcases p493_3 (m.d 0 1) (by simp) with h516 | h516
                                        · linarith only [h218, h516, hlam]
                                        · rcases p493_3 (m.d 0 2) (by simp) with h518 | h518
                                          · rcases p493_3 (m.d 0 3) (by simp) with h519 | h519
                                            · rcases p493_3 (m.d 0 4) (by simp) with h520 | h520
                                              · linarith only [h354, h520, hlam]
                                              · linarith only [h280, h520, hlam]
                                            · linarith only [h218, h519, hlam]
                                          · linarith only [h0, h518, hlam]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h351, hlam, p493_1]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        rcases p493_3 (m.d 0 1) (by simp) with h527 | h527
                                        · linarith only [h218, h527, hlam]
                                        · rcases p493_3 (m.d 0 2) (by simp) with h529 | h529
                                          · rcases p493_3 (m.d 0 3) (by simp) with h530 | h530
                                            · rcases p493_3 (m.d 0 4) (by simp) with h531 | h531
                                              · linarith only [h354, h531, hlam]
                                              · rcases p493_3 (m.d 0 5) (by simp) with h533 | h533
                                                · linarith only [h355, h533, hlam]
                                                · linarith only [h356, h533, hlam]
                                            · linarith only [h354, h530, hlam]
                                          · linarith only [h352, h529, hlam]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h355, h486, h487, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p493_1, u2ehi3]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h356, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p493_1]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h352, hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h354, hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h356, hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        rcases p493_3 (m.d 0 1) (by simp) with h544 | h544
                                        · linarith only [h349, h544, hlam]
                                        · rcases p493_3 (m.d 0 2) (by simp) with h546 | h546
                                          · rcases p493_3 (m.d 0 3) (by simp) with h547 | h547
                                            · rcases p493_3 (m.d 0 4) (by simp) with h548 | h548
                                              · linarith only [h356, h548, hlam]
                                              · linarith only [h280, h548, hlam]
                                            · linarith only [h218, h547, hlam]
                                          · linarith only [h0, h546, hlam]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h353, hlam, p493_1]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h355, hlam, p493_0]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [h352, h356, hc45, hlam, hphi, ht23, ht34, p493_1, u2ehi3]
                                      · have p493_0 := h493c.1
                                        have p493_1 := h493c.2.1
                                        have p493_2 := h493c.2.2.1
                                        have p493_3 := h493c.2.2.2
                                        linarith only [hlam, p493_0]
                              · linarith only [h354, h356, h486, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h0, h218, h351, h355, h485, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h351, h355, h484, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h351, h355, h483, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h351, h355, h482, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h562 | h562
                    · linarith only [h354, h355, h562, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
                                · linarith only [h351, h355, h569, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
                                  · linarith only [h352, h354, h355, h562, h564, h567, h571, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                                    · linarith only [h351, h352, h355, h562, h564, h567, h568, h573, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h0, hlam, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h218, hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h280, hlam, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h349, hlam, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        rcases p575_3 (m.d 0 1) (by simp) with h581 | h581
                                        · linarith only [h0, h581, hlam]
                                        · rcases p575_3 (m.d 0 2) (by simp) with h583 | h583
                                          · rcases p575_3 (m.d 0 3) (by simp) with h584 | h584
                                            · linarith only [h351, h584, hlam]
                                            · linarith only [h218, h584, hlam]
                                          · linarith only [h0, h583, hlam]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        rcases p575_3 (m.d 0 1) (by simp) with h589 | h589
                                        · linarith only [h0, h589, hlam]
                                        · rcases p575_3 (m.d 0 2) (by simp) with h591 | h591
                                          · rcases p575_3 (m.d 0 3) (by simp) with h592 | h592
                                            · linarith only [h351, h592, hlam]
                                            · rcases p575_3 (m.d 0 4) (by simp) with h594 | h594
                                              · linarith only [h352, h594, hlam]
                                              · rcases p575_3 (m.d 0 5) (by simp) with h596 | h596
                                                · linarith only [h353, h596, hlam]
                                                · linarith only [h355, h596, hlam]
                                          · linarith only [h351, h591, hlam]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        rcases p575_3 (m.d 0 1) (by simp) with h600 | h600
                                        · linarith only [h0, h600, hlam]
                                        · rcases p575_3 (m.d 0 2) (by simp) with h602 | h602
                                          · rcases p575_3 (m.d 0 3) (by simp) with h603 | h603
                                            · linarith only [h351, h603, hlam]
                                            · linarith only [h354, h603, hlam]
                                          · linarith only [h352, h602, hlam]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h353, hc02, hlam, hphi, ht0b, ht5b, p575_1, u5ehi2]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h355, h564, h567, hc01, hc12, hlam, hphi, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h351, hlam, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h352, h355, h564, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p575_1, u2ehi3]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h355, hlam, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h354, h355, h564, h567, hc01, hc12, hlam, hphi, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h352, hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h354, hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h562, hlam, p575_0]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h355, h564, h567, hc01, hc12, hlam, hphi, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h353, hlam, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h351, h355, h564, h567, h568, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p575_1]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [h352, h355, h564, h567, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p575_1, u2ehi3]
                                      · have p575_0 := h575c.1
                                        have p575_1 := h575c.2.1
                                        have p575_2 := h575c.2.2.1
                                        have p575_3 := h575c.2.2.2
                                        linarith only [hlam, p575_0]
                              · linarith only [h354, h355, h564, h567, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                                · linarith only [h218, h567, h625, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                                  · linarith only [h0, h352, h627, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h629 | h629
                                    · linarith only [h218, h351, h562, h567, h624, h629, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                    · rcases h0bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h0, hlam, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h218, hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h280, hlam, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h349, hlam, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        rcases p631_3 (m.d 0 1) (by simp) with h637 | h637
                                        · linarith only [h0, h637, hlam]
                                        · rcases p631_3 (m.d 0 2) (by simp) with h639 | h639
                                          · rcases p631_3 (m.d 0 3) (by simp) with h640 | h640
                                            · linarith only [h351, h640, hlam]
                                            · linarith only [h218, h640, hlam]
                                          · linarith only [h0, h639, hlam]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        rcases p631_3 (m.d 0 1) (by simp) with h645 | h645
                                        · linarith only [h0, h645, hlam]
                                        · rcases p631_3 (m.d 0 2) (by simp) with h647 | h647
                                          · rcases p631_3 (m.d 0 3) (by simp) with h648 | h648
                                            · linarith only [h351, h648, hlam]
                                            · rcases p631_3 (m.d 0 4) (by simp) with h650 | h650
                                              · linarith only [h352, h650, hlam]
                                              · rcases p631_3 (m.d 0 5) (by simp) with h652 | h652
                                                · linarith only [h353, h652, hlam]
                                                · linarith only [h355, h652, hlam]
                                          · linarith only [h351, h647, hlam]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        rcases p631_3 (m.d 0 1) (by simp) with h656 | h656
                                        · linarith only [h0, h656, hlam]
                                        · rcases p631_3 (m.d 0 2) (by simp) with h658 | h658
                                          · rcases p631_3 (m.d 0 3) (by simp) with h659 | h659
                                            · linarith only [h351, h659, hlam]
                                            · linarith only [h354, h659, hlam]
                                          · linarith only [h352, h658, hlam]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h0, h353, hc12, hlam, hphi, ht01, ht0b, ht5b, p631_1, u5ehi2]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h218, h567, hc01, hc35, hlam, hphi, ht12, ht23, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h351, hlam, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h218, h352, h567, h629, hc45, hlam, hphi, ht23, ht34, p631_1, u2ehi3]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h355, hlam, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h218, h354, h567, h629, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h352, hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h354, hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h562, hlam, p631_0]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        rcases p631_3 (m.d 0 1) (by simp) with h674 | h674
                                        · linarith only [h349, h674, hlam]
                                        · rcases p631_3 (m.d 0 2) (by simp) with h676 | h676
                                          · rcases p631_3 (m.d 0 3) (by simp) with h677 | h677
                                            · linarith only [h355, h677, hlam]
                                            · linarith only [h218, h677, hlam]
                                          · linarith only [h0, h676, hlam]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h353, hlam, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h351, h355, h624, h629, hc34, hc45, hlam, hphi, p631_1]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [h352, h355, h629, hc45, hlam, hphi, ht23, ht34, p631_1, u2ehi3]
                                      · have p631_0 := h631c.1
                                        have p631_1 := h631c.2.1
                                        have p631_2 := h631c.2.2.1
                                        have p631_3 := h631c.2.2.2
                                        linarith only [hlam, p631_0]
                              · linarith only [h354, h355, h624, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h0, h353, h566, hlam]
                        · linarith only [h0, h352, h353, h565, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h353, h564, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h689 | h689
                  · linarith only [h354, h689, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h691 | h691
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h692 | h692
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h693 | h693
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h694 | h694
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h695 | h695
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h696 | h696
                              · linarith only [h351, h354, h696, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h698 | h698
                                · linarith only [h351, h689, h698, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h700 | h700
                                  · linarith only [h352, h700, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h354, h691, h700, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                              · linarith only [h351, h354, h691, h703, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h705 | h705
                                · linarith only [h218, h695, h703, h705, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                                  · linarith only [h0, h352, h707, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · linarith only [h354, h691, h707, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h280, h691, h693, h694, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h0, h352, h691, h693, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h351, h352, h691, h692, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h713 | h713
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h714 | h714
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h715 | h715
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h717 | h717
                              · linarith only [h351, h354, h717, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h719 | h719
                                · linarith only [h351, h689, h719, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h721 | h721
                                  · linarith only [h352, h691, h721, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h723 | h723
                                    · linarith only [h352, h691, h723, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h351, h354, h723, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h726 | h726
                              · linarith only [h351, h354, h726, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h728 | h728
                                · linarith only [h351, h354, h716, h728, hc13, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h730 | h730
                                  · linarith only [h352, h730, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h732 | h732
                                    · linarith only [h352, h691, h732, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h351, h354, h732, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h0, h351, h715, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h352, h353, h714, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h351, h353, h713, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h351, h353, hc25, hlam, hphi, u2ehi2]
            · linarith only [h351, h352, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h740 | h740
            · linarith only [h351, h740, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h742 | h742
              · linarith only [h351, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h744 | h744
                · rcases m.htr 0 3 5 (by decide) (by decide) with h745 | h745
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h746 | h746
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
                      · linarith only [h351, h744, h746, h747, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h749 | h749
                        · linarith only [h740, h747, h749, hc23, hlam, hphi, u2ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
                          · linarith only [h742, h747, h751, hc23, hlam, hphi, u2ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h754 | h754
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h755 | h755
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h756 | h756
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h757 | h757
                                    · linarith only [h218, h744, h747, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                    · rcases h0bigk with h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h0, hlam, p759_1]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h218, hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h280, hlam, p759_1]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h349, hlam, p759_1]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h0, h751, h754, h756, hc01, hc23, hlam, hphi, ht12, p759_1]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h351, hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h740, hlam, p759_1]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h742, hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        rcases p759_3 (m.d 0 1) (by simp) with h770 | h770
                                        · linarith only [h218, h770, hlam]
                                        · rcases p759_3 (m.d 0 2) (by simp) with h772 | h772
                                          · linarith only [h351, h772, hlam]
                                          · linarith only [h0, h772, hlam]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h218, h747, hc23, hlam, hphi, p759_1, u2ehi0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h218, h740, h747, hc23, hlam, hphi, p759_1, u2ehi0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h218, h746, h747, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u5ehi3]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        rcases p759_3 (m.d 0 1) (by simp) with h779 | h779
                                        · linarith only [h280, h779, hlam]
                                        · rcases p759_3 (m.d 0 2) (by simp) with h781 | h781
                                          · linarith only [h740, h781, hlam]
                                          · linarith only [h0, h781, hlam]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h280, h749, h754, hc23, hlam, hphi, p759_1, u2ehi0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h744, hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h280, h746, h749, h754, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p759_1, u5ehi3]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        rcases p759_3 (m.d 0 1) (by simp) with h788 | h788
                                        · linarith only [h349, h788, hlam]
                                        · rcases p759_3 (m.d 0 2) (by simp) with h790 | h790
                                          · linarith only [h742, h790, hlam]
                                          · linarith only [h0, h790, hlam]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h742, h754, h756, hc23, hlam, hphi, p759_1, u2ehi0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h745, hlam, p759_0]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [h746, hlam, p759_1]
                                      · have p759_0 := h759c.1
                                        have p759_1 := h759c.2.1
                                        have p759_2 := h759c.2.2.1
                                        have p759_3 := h759c.2.2.2
                                        linarith only [hlam, p759_0]
                                  · linarith only [h740, h756, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h351, h755, hc35, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h218, h745, h747, h754, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h218, h744, h746, h753, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
                      · linarith only [h351, h745, h801, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
                        · linarith only [h801, h803, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h805 | h805
                          · linarith only [h801, h805, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h807 | h807
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h808 | h808
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h809 | h809
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h810 | h810
                                  · linarith only [h740, h746, h808, h810, hc23, hlam, hphi, u2ehi0]
                                  · linarith only [h803, h810, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h218, h351, h745, h809, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h218, h745, h801, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h218, h745, h807, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h816 | h816
                    · linarith only [h744, h745, h816, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h818 | h818
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h819 | h819
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h820 | h820
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h821 | h821
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h822 | h822
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h823 | h823
                                · linarith only [h740, h744, h745, h818, h823, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · linarith only [h351, h823, hc35, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h351, h744, h822, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h351, h818, h821, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h351, h818, h820, hc25, hlam, hphi, u2ehi0]
                        · linarith only [h351, h818, h819, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h830 | h830
                        · linarith only [h818, h830, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
                          · linarith only [h818, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h834 | h834
                            · linarith only [h351, h745, h818, h834, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h837 | h837
                                · linarith only [h818, h834, h837, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h351, h837, hc35, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h0, h818, h836, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h841 | h841
                  · linarith only [h744, h841, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h844 | h844
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h845 | h845
                        · linarith only [h740, h843, h845, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h351, h844, h845, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h848 | h848
                        · linarith only [h844, h848, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h850 | h850
                          · linarith only [h844, h850, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h852 | h852
                            · linarith only [h351, h841, h844, h852, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h854 | h854
                              · linarith only [h351, h744, h854, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h351, h854, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h858 | h858
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h859 | h859
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h861 | h861
                              · linarith only [h351, h744, h861, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h351, h861, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h351, h857, h860, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h858, h859, hc25, hlam, hphi, u2ehi3]
                        · linarith only [h351, h857, h858, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
                        · linarith only [h857, h867, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h869 | h869
                          · linarith only [h857, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h871 | h871
                            · linarith only [h351, h841, h857, h871, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h873 | h873
                              · linarith only [h351, h744, h873, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h351, h873, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
