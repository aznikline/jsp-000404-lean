import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h14, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h17, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
            · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h22, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h24, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h1, h22, h26, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                      · linarith only [h1, h28, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h20, h22, h28, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                · linarith only [h0, h20, h31, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h33, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h1, h31, h35, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                      · linarith only [h1, h37, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h20, h31, h37, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · linarith only [h0, h4, h41, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h43, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h1, h41, h45, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                      · linarith only [h1, h20, h4, h47, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h2, h47, h49, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h40, h41, h49, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                · linarith only [h0, h4, h52, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                  · linarith only [h1, h52, h54, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h1, h52, h56, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                      · linarith only [h1, h20, h4, h58, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                        · linarith only [h1, h40, h60, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h2, h62, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                                · linarith only [h58, h62, h66, hc13, hlam, hphi, ht34, u4elo2]
                                · linarith only [h54, h66, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h0, h20, h4, h64, h65, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h4, h64, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h71 | h71
          · rcases m.htr 0 3 4 (by decide) (by decide) with h72 | h72
            · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
              · linarith only [h0, h3, h71, h73, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                · linarith only [h0, h3, h75, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h71, h75, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h78 | h78
              · linarith only [h0, h3, h71, h72, h78, hc23, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                · linarith only [h0, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h71, h80, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
            · rcases m.htr 0 3 5 (by decide) (by decide) with h84 | h84
              · linarith only [h1, h3, h84, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                · linarith only [h0, h3, h71, h86, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h0, h3, h88, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h1, h3, h86, h90, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                      · linarith only [h1, h3, h92, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h1, h3, h83, h86, h92, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h95 | h95
              · linarith only [h2, h3, h83, h95, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
                · linarith only [h0, h71, h97, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h1, h97, h99, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                    · linarith only [h1, h101, h3, h97, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                      · linarith only [h1, h103, h3, h83, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                        · linarith only [h103, h105, h2, h3, h95, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h107, h2, h3, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
                          · linarith only [h103, h107, h2, h3, h97, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h111 | h111
      · rcases m.htr 0 1 5 (by decide) (by decide) with h112 | h112
        · rcases m.htr 0 2 3 (by decide) (by decide) with h113 | h113
          · linarith only [h0, h1, h113, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h115 | h115
            · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
              · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                · linarith only [h0, h113, h117, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                  · linarith only [h0, h119, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                    · linarith only [h1, h111, h119, h121, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h1, h111, h125, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                                · linarith only [h119, h125, h129, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h119, h129, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h112, h117, h124, h128, hlam]
                            · linarith only [h1, h112, h117, h123, h125, h127, hlam]
                        · linarith only [h0, h1, h124, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h115, h123, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1, h112, h116, hlam]
            · linarith only [h0, h1, h115, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h138 | h138
          · linarith only [h0, h1, h138, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
            · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
              · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
                · linarith only [h0, h138, h142, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                  · linarith only [h0, h112, h141, h144, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                    · linarith only [h111, h112, h141, h144, h146, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h111, h112, h141, h150, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h111, h112, h144, h150, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h141, h149, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1, h111, h144, h148, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                · linarith only [h0, h155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                  · linarith only [h0, h1, h141, h157, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                    · linarith only [h1, h111, h141, h157, h159, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                        · linarith only [h1, h111, h141, h155, h157, h162, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h111, h157, h162, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h111, h157, h161, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h111, h140, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h111, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h168 | h168
    · rcases m.htr 0 1 4 (by decide) (by decide) with h169 | h169
      · rcases m.htr 0 1 5 (by decide) (by decide) with h170 | h170
        · rcases m.htr 0 2 3 (by decide) (by decide) with h171 | h171
          · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
            · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
              · rcases m.htr 1 2 3 (by decide) (by decide) with h174 | h174
                · rcases m.htr 1 2 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h177 | h177
                      · linarith only [h168, h177, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h168, h172, h177, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h170, h176, hlam]
                  · linarith only [h0, h175, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h168, h171, h174, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                      · linarith only [h168, h186, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h172, h186, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h170, h185, hlam]
                  · linarith only [h0, h184, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h168, h171, h183, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h192 | h192
              · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                      · linarith only [h168, h172, h196, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
                        · linarith only [h0, h168, h198, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h192, h198, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h170, h195, hlam]
                  · linarith only [h0, h194, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h168, h171, h193, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h207 | h207
                      · linarith only [h168, h172, h207, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                        · linarith only [h168, h192, h209, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                          · linarith only [h0, h169, h211, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                            · linarith only [h168, h172, h204, h213, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                              · linarith only [h168, h192, h204, h215, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h217 | h217
                                · linarith only [h211, h217, hc14, hlam, hphi, u4elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h219 | h219
                                  · linarith only [h204, h207, h211, h219, hc23, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h168, h172, h204, h219, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h170, h206, hlam]
                  · linarith only [h0, h205, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h168, h171, h204, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h168, h171, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h226 | h226
          · rcases m.htr 0 3 4 (by decide) (by decide) with h227 | h227
            · rcases m.htr 0 3 5 (by decide) (by decide) with h228 | h228
              · linarith only [h168, h170, h228, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
                · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                      · linarith only [h168, h233, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h168, h227, h233, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h168, h232, h236, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h168, h227, h232, h236, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h231, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h168, h226, h227, h230, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h241 | h241
              · linarith only [h168, h170, h227, h241, hc13, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                      · linarith only [h168, h227, h246, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                        · linarith only [h168, h170, h227, h241, h248, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                          · linarith only [h169, h250, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h169, h170, h246, h250, hc13, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h168, h227, h253, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h0, h169, h245, h253, h255, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h257 | h257
                          · linarith only [h0, h169, h245, h257, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h169, h243, h245, h253, h257, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h244, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h168, h226, h243, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h168, h226, hlam]
      · linarith only [h168, h169, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h264 | h264
      · rcases m.htr 0 1 5 (by decide) (by decide) with h265 | h265
        · rcases m.htr 0 2 3 (by decide) (by decide) with h266 | h266
          · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
            · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
              · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                          · linarith only [h264, h274, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                            · linarith only [h266, h276, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h266, h267, h276, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h168, h266, h268, h273, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h168, h264, h270, h272, hc24, hlam, hphi, u4elo3]
                    · linarith only [h168, h265, h269, h271, hlam]
                  · linarith only [h168, h269, h270, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h264, h266, h269, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h168, h265, h268, hlam]
            · linarith only [h168, h264, h267, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h286 | h286
            · rcases m.htr 0 3 5 (by decide) (by decide) with h287 | h287
              · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h290 | h290
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h264, h293, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h297 | h297
                                · linarith only [h289, h293, h297, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                                  · linarith only [h289, h293, h295, h299, hlam]
                                  · rcases h1bigk with h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c | h301c
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h168, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, h266, hc14, hlam, hphi, ht0b, ht45, ht5b, p301_1, u0elo2]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, h266, hc15, hlam, hphi, ht0b, ht5b, p301_1, u0elo2]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      rcases p301_3 (m.d 0 1) (by simp) with h307 | h307
                                      · linarith only [h307, hlam, p301_0]
                                      · rcases p301_3 (m.d 1 2) (by simp) with h309 | h309
                                        · rcases p301_3 (m.d 1 3) (by simp) with h310 | h310
                                          · linarith only [h288, h310, hlam]
                                          · linarith only [h168, h310, hlam]
                                        · linarith only [h309, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, h266, h288, hc01, hc12, hlam, hphi, p301_1]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, h265, h266, h288, h293, hlam, p301_2]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, h265, h266, h288, hlam, p301_2]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      rcases p301_3 (m.d 0 1) (by simp) with h318 | h318
                                      · linarith only [h318, hlam, p301_0]
                                      · rcases p301_3 (m.d 1 2) (by simp) with h320 | h320
                                        · rcases p301_3 (m.d 1 3) (by simp) with h321 | h321
                                          · rcases p301_3 (m.d 1 4) (by simp) with h322 | h322
                                            · linarith only [h291, h322, hlam]
                                            · rcases p301_3 (m.d 1 5) (by simp) with h324 | h324
                                              · linarith only [h292, h324, hlam]
                                              · rcases h3bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h168, hlam, p326_1]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h266, hlam, p326_1]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1, u0elo2]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h299, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1, u0elo2]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  rcases p326_3 (m.d 0 3) (by simp) with h332 | h332
                                                  · linarith only [h168, h332, hlam]
                                                  · rcases p326_3 (m.d 1 3) (by simp) with h334 | h334
                                                    · rcases p326_3 (m.d 2 3) (by simp) with h335 | h335
                                                      · linarith only [h288, h335, hlam]
                                                      · linarith only [h266, h335, hlam]
                                                    · linarith only [h168, h334, hlam]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h0, h265, h266, h288, h289, h293, h295, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p326_1]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h265, h289, h293, h295, hlam, p301_1, p326_2]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h265, h292, hlam, p301_1, p326_2]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h0, h265, h266, h288, h289, h293, h295, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p326_1]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h288, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  rcases p326_3 (m.d 0 3) (by simp) with h346 | h346
                                                  · linarith only [h266, h346, hlam]
                                                  · linarith only [h286, h346, hlam]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  rcases p326_3 (m.d 0 3) (by simp) with h349 | h349
                                                  · linarith only [h266, h349, hlam]
                                                  · linarith only [h287, h349, hlam]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h286, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h291, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h295, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h299, hlam, p326_1]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h287, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h292, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h296, hlam, p326_0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [h265, h290, h296, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1, u0elo0]
                                                · have p326_0 := h326c.1
                                                  have p326_1 := h326c.2.1
                                                  have p326_2 := h326c.2.2.1
                                                  have p326_3 := h326c.2.2.2
                                                  linarith only [hlam, p326_0]
                                          · linarith only [h321, hlam, p301_0]
                                        · linarith only [h0, h320, hlam]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h288, hlam, p301_1]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      rcases p301_3 (m.d 0 1) (by simp) with h366 | h366
                                      · linarith only [h168, h366, hlam]
                                      · linarith only [h264, h366, hlam]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      rcases p301_3 (m.d 0 1) (by simp) with h369 | h369
                                      · linarith only [h168, h369, hlam]
                                      · linarith only [h265, h369, hlam]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h264, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h289, hlam, p301_1]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h291, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h293, hlam, p301_1]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h265, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h290, hlam, p301_1]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h292, hlam, p301_0]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [h0, h265, h266, h289, h295, hc34, hlam, hphi, ht0b, ht45, ht5b, p301_1, u0elo2]
                                    · have p301_0 := h301c.1
                                      have p301_1 := h301c.2.1
                                      have p301_2 := h301c.2.2.1
                                      have p301_3 := h301c.2.2.2
                                      linarith only [hlam, p301_0]
                              · linarith only [h0, h266, h287, h296, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h265, h266, h289, h293, h295, hc24, hlam, hphi, u4elo3]
                        · linarith only [h287, h292, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h266, h288, h291, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h264, h266, h288, h289, h290, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h266, h288, h289, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                          · linarith only [h264, h392, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h396 | h396
                                · linarith only [h388, h392, h396, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h398 | h398
                                  · linarith only [h388, h392, h394, h398, hlam]
                                  · rcases h1bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h0, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h168, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h0, h288, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h0, h288, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h288, hc01, hc23, hlam, hphi, ht12, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h288, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      rcases p400_3 (m.d 0 1) (by simp) with h409 | h409
                                      · linarith only [h0, h409, hlam]
                                      · linarith only [h264, h409, hlam]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      rcases p400_3 (m.d 0 1) (by simp) with h412 | h412
                                      · linarith only [h0, h412, hlam]
                                      · linarith only [h265, h412, hlam]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      rcases p400_3 (m.d 0 1) (by simp) with h415 | h415
                                      · linarith only [h415, hlam, p400_0]
                                      · rcases p400_3 (m.d 1 2) (by simp) with h417 | h417
                                        · linarith only [h288, h417, hlam]
                                        · linarith only [h0, h417, hlam]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h0, h265, h388, h392, h394, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      rcases p400_3 (m.d 0 1) (by simp) with h422 | h422
                                      · linarith only [h168, h422, hlam]
                                      · linarith only [h264, h422, hlam]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      rcases p400_3 (m.d 0 1) (by simp) with h425 | h425
                                      · linarith only [h168, h425, hlam]
                                      · linarith only [h265, h425, hlam]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h264, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h388, hlam, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h390, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h392, hlam, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h265, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h389, hlam, p400_1]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h391, hlam, p400_0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [h265, h388, h394, hc34, hlam, hphi, ht0b, ht45, ht5b, p400_1, u0elo0]
                                    · have p400_0 := h400c.1
                                      have p400_1 := h400c.2.1
                                      have p400_2 := h400c.2.2.1
                                      have p400_3 := h400c.2.2.2
                                      linarith only [hlam, p400_0]
                              · linarith only [h0, h266, h287, h395, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h168, h265, h288, h388, h392, h394, hc24, hlam, hphi, u4elo3]
                        · linarith only [h287, h391, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h264, h288, h388, h390, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h265, h389, hlam]
                  · linarith only [h0, h388, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h168, h265, h287, hlam]
            · linarith only [h0, h264, h266, h286, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h446 | h446
          · rcases m.htr 0 3 4 (by decide) (by decide) with h447 | h447
            · rcases m.htr 0 3 5 (by decide) (by decide) with h448 | h448
              · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
                · rcases m.htr 1 2 4 (by decide) (by decide) with h450 | h450
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
                          · linarith only [h264, h454, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h264, h265, h454, hc14, hlam, hphi, u4elo4]
                        · linarith only [h446, h448, h453, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h168, h264, h450, h452, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                        · linarith only [h449, h451, h460, hlam]
                        · linarith only [h168, h264, h446, h448, h450, h460, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h168, h264, h450, h459, hc24, hlam, hphi, u4elo3]
                  · linarith only [h168, h449, h450, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h264, h446, h449, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
                · rcases m.htr 1 2 4 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h471 | h471
                          · linarith only [h264, h471, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h264, h265, h471, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                          · linarith only [h168, h264, h470, h474, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h168, h264, h469, h470, h474, hc34, hlam, hphi, u4elo4]
                      · linarith only [h168, h469, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h479 | h479
                        · linarith only [h168, h264, h448, h466, h467, h468, h479, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                          · linarith only [h264, h481, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h168, h264, h466, h468, h481, hc14, hlam, hphi, u4elo4]
                      · linarith only [h168, h264, h467, h478, hc24, hlam, hphi, u4elo3]
                  · linarith only [h168, h466, h467, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h264, h446, h466, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h168, h264, h447, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h488 | h488
            · rcases m.htr 0 3 5 (by decide) (by decide) with h489 | h489
              · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
                          · linarith only [h264, h495, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h264, h265, h493, h495, hc34, hlam, hphi, u4elo4]
                        · linarith only [h0, h264, h446, h489, h490, h493, h494, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h264, h446, h490, h491, h493, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h264, h446, h490, h491, h492, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h446, h490, h491, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h506 | h506
                          · linarith only [h264, h506, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h264, h265, h506, hc14, hlam, hphi, u4elo4]
                        · linarith only [h489, h505, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h264, h265, h490, h502, h503, h504, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h511 | h511
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                          · linarith only [h264, h513, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h264, h502, h503, h513, hc24, hlam, hphi, u4elo4]
                        · linarith only [h0, h264, h489, h490, h502, h512, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h264, h490, h502, h511, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h502, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h521 | h521
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h524 | h524
                          · linarith only [h264, h524, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h264, h446, h489, h523, h524, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                          · linarith only [h0, h264, h446, h519, h523, h527, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h264, h265, h522, h527, hc34, hlam, hphi, u4elo4]
                      · linarith only [h0, h264, h446, h519, h522, hc14, hlam, hphi, u4elo3]
                    · linarith only [h0, h264, h446, h519, h520, h521, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h264, h446, h519, h520, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h533 | h533
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                          · linarith only [h264, h537, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h264, h446, h489, h536, h537, hc14, hlam, hphi, u4elo4]
                        · linarith only [h519, h534, h536, hlam]
                      · linarith only [h264, h265, h519, h533, h534, h535, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h543 | h543
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                          · linarith only [h264, h544, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h264, h446, h489, h543, h544, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h547 | h547
                          · linarith only [h0, h264, h519, h543, h547, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h264, h265, h533, h547, hc24, hlam, hphi, u4elo4]
                      · linarith only [h0, h264, h519, h533, h542, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h533, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h264, h446, h488, hc14, hlam, hphi, u4elo3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h553 | h553
        · rcases m.htr 0 2 3 (by decide) (by decide) with h554 | h554
          · rcases m.htr 0 3 4 (by decide) (by decide) with h555 | h555
            · rcases m.htr 0 3 5 (by decide) (by decide) with h556 | h556
              · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h559 | h559
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h561 | h561
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h562 | h562
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                            · linarith only [h264, h553, h554, h559, h563, hc25, hc34, hlam, hphi, ht0b, ht5b, u0elo1, u4elo1]
                            · linarith only [h264, h553, h555, h559, h563, hc23, hc25, hlam, hphi, ht0b, ht34, ht5b, u0elo2, u4elo1]
                          · linarith only [h264, h553, h559, h562, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h264, h553, h554, h556, h559, h560, h561, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h554, h555, h560, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h168, h553, h557, h559, hlam]
                  · linarith only [h168, h553, h557, h558, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                · linarith only [h554, h557, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h264, h553, h555, h556, hc34, hlam, hphi, u4elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h573 | h573
              · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h579 | h579
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                            · linarith only [h168, h553, h554, h555, h576, h580, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h582 | h582
                              · linarith only [h554, h582, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h555, h573, h577, h582, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h168, h553, h555, h576, h577, h579, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h168, h553, h555, h576, h577, h578, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h168, h553, h576, h577, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h168, h553, h574, h576, hlam]
                  · linarith only [h168, h574, h575, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h553, h554, h574, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h168, h553, h573, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h592 | h592
            · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
              · rcases m.htr 1 2 3 (by decide) (by decide) with h594 | h594
                · rcases m.htr 1 2 4 (by decide) (by decide) with h595 | h595
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h596 | h596
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h599 | h599
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h602 | h602
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h603 | h603
                                  · linarith only [h592, h603, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h599, h603, hc34, hlam, hphi, u4elo1]
                                · linarith only [h264, h553, h599, h602, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h553, h554, h593, h596, h601, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h0, h553, h554, h596, h600, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h264, h553, h596, h599, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h0, h553, h554, h593, h594, h596, h598, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h553, h554, h592, h594, h596, h597, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h554, h594, h596, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h553, h554, h594, h595, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h614 | h614
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h615 | h615
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h616 | h616
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h617 | h617
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h618 | h618
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h620 | h620
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h621 | h621
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h622 | h622
                                  · linarith only [h592, h622, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h618, h622, hc34, hlam, hphi, u4elo1]
                                · linarith only [h553, h618, h621, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h594, h620, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h264, h553, h594, h614, h615, h619, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h264, h553, h615, h618, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h264, h553, h593, h594, h614, h615, h617, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h264, h553, h592, h594, h614, h615, h616, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h264, h553, h614, h615, hlam]
                  · linarith only [h0, h614, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h264, h553, h592, h593, hc34, hlam, hphi, u4elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h634 | h634
              · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h639 | h639
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h640 | h640
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
                            · linarith only [h0, h554, h592, h635, h641, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h553, h554, h637, h638, h641, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h592, h638, h640, hc03, hlam, hphi, ht34, u4elo4]
                        · linarith only [h634, h639, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h553, h554, h635, h637, h638, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h0, h554, h635, h637, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h553, h554, h635, h636, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h652 | h652
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h653 | h653
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
                            · linarith only [h0, h553, h554, h592, h635, h649, h650, h654, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h635, h649, h651, h654, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h553, h554, h592, h650, h651, h653, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h0, h553, h554, h592, h650, h651, h652, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h168, h553, h650, h651, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h0, h553, h650, hlam]
                  · linarith only [h0, h553, h649, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · linarith only [h0, h553, h554, h634, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h663 | h663
          · rcases m.htr 0 3 4 (by decide) (by decide) with h664 | h664
            · rcases m.htr 0 3 5 (by decide) (by decide) with h665 | h665
              · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                            · linarith only [h663, h672, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h664, h672, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h264, h671, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h264, h663, h665, h669, h670, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h663, h664, h669, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h679 | h679
                        · linarith only [h666, h668, h679, hlam]
                        · linarith only [h168, h665, h679, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h168, h664, h678, hlam]
                  · linarith only [h0, h663, h664, h667, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h663, h666, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h685 | h685
                · rcases m.htr 1 2 4 (by decide) (by decide) with h686 | h686
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h687 | h687
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h688 | h688
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h689 | h689
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h690 | h690
                          · linarith only [h664, h665, h689, h690, hc34, hlam, hphi, u4elo1]
                          · linarith only [h264, h690, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h693 | h693
                          · linarith only [h688, h689, h693, hlam]
                          · linarith only [h264, h693, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h664, h688, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h698 | h698
                        · linarith only [h664, h665, h685, h687, h698, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h700 | h700
                          · linarith only [h686, h687, h700, hlam]
                          · linarith only [h264, h700, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h664, h697, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h663, h686, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h663, h685, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h706 | h706
              · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
                · rcases m.htr 1 2 4 (by decide) (by decide) with h708 | h708
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h709 | h709
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h711 | h711
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
                            · linarith only [h663, h664, h706, h713, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h715 | h715
                              · linarith only [h663, h715, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h706, h715, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h664, h710, h712, hc03, hlam, hphi, ht34, u4elo4]
                        · linarith only [h664, h706, h710, h711, hlam]
                      · linarith only [h168, h710, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h721 | h721
                      · linarith only [h664, h706, h707, h709, h721, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h168, h721, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h708, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h663, h707, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
                · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h730 | h730
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                            · linarith only [h663, h664, h732, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
                              · linarith only [h663, h706, h734, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h737 | h737
                                  · rcases h1bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h0, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h168, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h264, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h553, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      rcases p738_3 (m.d 0 1) (by simp) with h744 | h744
                                      · linarith only [h744, hlam, p738_0]
                                      · rcases p738_3 (m.d 1 2) (by simp) with h746 | h746
                                        · rcases p738_3 (m.d 1 3) (by simp) with h747 | h747
                                          · linarith only [h726, h747, hlam]
                                          · linarith only [h168, h747, hlam]
                                        · linarith only [h746, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h168, h706, h729, h737, hc01, hc12, hlam, hphi, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h264, hc01, hc12, hlam, hphi, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h553, hc01, hc12, hlam, hphi, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      rcases p738_3 (m.d 0 1) (by simp) with h755 | h755
                                      · linarith only [h755, hlam, p738_0]
                                      · rcases p738_3 (m.d 1 2) (by simp) with h757 | h757
                                        · rcases p738_3 (m.d 1 3) (by simp) with h758 | h758
                                          · rcases p738_3 (m.d 1 4) (by simp) with h759 | h759
                                            · linarith only [h729, h759, hlam]
                                            · linarith only [h264, h759, hlam]
                                          · linarith only [h758, hlam, p738_0]
                                        · linarith only [h0, h757, hlam]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h726, hlam, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h168, h706, h729, h737, hc01, hc13, hlam, hphi, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h168, h706, h726, h730, hc01, hc12, hlam, hphi, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p738_1, u4elo1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h727, hlam, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h729, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h168, h706, h730, hc01, hlam, hphi, ht12, ht23, ht34, p738_1, u4elo1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h731, hc01, hlam, hphi, ht12, ht23, ht34, p738_1, u4elo1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h728, hlam, p738_1]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h730, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [h731, hlam, p738_0]
                                    · have p738_0 := h738c.1
                                      have p738_1 := h738c.2.1
                                      have p738_2 := h738c.2.2.1
                                      have p738_3 := h738c.2.2.2
                                      linarith only [hlam, p738_0]
                                  · linarith only [h732, h736, h737, hlam]
                                · linarith only [h731, h736, hc24, hlam, hphi, u4elo1]
                          · linarith only [h264, h731, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h168, h664, h729, h730, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h168, h729, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                      · linarith only [h168, h664, h726, h728, h783, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h168, h783, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h727, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h663, h726, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h788 | h788
            · rcases m.htr 0 3 5 (by decide) (by decide) with h789 | h789
              · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                · rcases m.htr 1 2 4 (by decide) (by decide) with h791 | h791
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h792 | h792
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h795 | h795
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h796 | h796
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h797 | h797
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h798 | h798
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                                  · linarith only [h788, h799, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h795, h799, hc34, hlam, hphi, u4elo1]
                                · linarith only [h795, h798, hc24, hlam, hphi, u4elo1]
                              · linarith only [h0, h663, h789, h797, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h663, h796, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h264, h795, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h663, h789, h790, h794, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h663, h788, h790, h793, hlam]
                    · linarith only [h0, h663, h790, h792, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h663, h790, h791, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h810 | h810
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h811 | h811
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h813 | h813
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h814 | h814
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h816 | h816
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                                  · linarith only [h788, h818, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                  · linarith only [h790, h810, h817, h818, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h814, h817, hc24, hlam, hphi, u4elo1]
                              · linarith only [h789, h790, h816, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h790, h815, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h264, h814, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h789, h813, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h264, h788, h790, h810, h812, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h827 | h827
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h828 | h828
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h829 | h829
                          · linarith only [h810, h811, h829, hlam]
                          · linarith only [h264, h829, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h168, h789, h828, hlam]
                      · linarith only [h168, h788, h827, hlam]
                  · linarith only [h0, h810, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
                · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h840 | h840
                          · linarith only [h788, h789, h839, h840, hc34, hlam, hphi, u4elo1]
                          · linarith only [h264, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                          · linarith only [h838, h839, h843, hlam]
                          · linarith only [h264, h843, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h0, h663, h788, h835, h838, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h663, h835, h837, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h663, h835, h836, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h849 | h849
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h850 | h850
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h852 | h852
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h853 | h853
                          · linarith only [h788, h789, h852, h853, hc34, hlam, hphi, u4elo1]
                          · linarith only [h264, h853, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h835, h850, h852, hlam]
                      · linarith only [h788, h835, h851, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h858 | h858
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h859 | h859
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h860 | h860
                          · linarith only [h788, h789, h859, h860, hc34, hlam, hphi, u4elo1]
                          · linarith only [h264, h860, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h863 | h863
                          · linarith only [h849, h850, h863, hlam]
                          · linarith only [h264, h863, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h788, h835, h858, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h849, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
              · rcases m.htr 1 2 3 (by decide) (by decide) with h869 | h869
                · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h871 | h871
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h872 | h872
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h875 | h875
                            · linarith only [h788, h868, h869, h875, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h663, h872, h875, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                          · linarith only [h788, h868, h872, h874, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h788, h868, h872, h873, hlam]
                      · linarith only [h168, h872, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h663, h869, h871, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h663, h869, h870, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h883 | h883
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h884 | h884
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h885 | h885
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h886 | h886
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h888 | h888
                            · linarith only [h788, h868, h869, h883, h888, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h869, h883, h885, h888, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h788, h868, h885, h887, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h868, h886, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h869, h885, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h894 | h894
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h895 | h895
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h896 | h896
                          · linarith only [h883, h884, h896, hlam]
                          · linarith only [h788, h894, h896, hc03, hlam, hphi, ht34, u4elo4]
                        · linarith only [h788, h868, h894, h895, hlam]
                      · linarith only [h168, h894, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h883, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                · rcases m.htr 1 2 4 (by decide) (by decide) with h903 | h903
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h904 | h904
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h905 | h905
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h906 | h906
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h907 | h907
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h908 | h908
                            · linarith only [h0, h663, h788, h902, h908, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h663, h905, h908, hc01, hc13, hlam, hphi]
                          · linarith only [h264, h907, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h663, h788, h905, h906, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h168, h905, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h663, h902, h904, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h663, h902, h903, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h916 | h916
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h917 | h917
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h918 | h918
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h919 | h919
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h920 | h920
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h921 | h921
                            · linarith only [h0, h663, h788, h902, h916, h921, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h902, h916, h918, h921, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h663, h788, h918, h920, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h663, h788, h918, h919, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h168, h918, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h929 | h929
                          · linarith only [h916, h917, h929, hlam]
                          · linarith only [h264, h929, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h663, h788, h927, h928, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h168, h927, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h916, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

end R2N4
