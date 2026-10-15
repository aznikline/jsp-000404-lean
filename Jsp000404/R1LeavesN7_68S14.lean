import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h3ehi := hb3.1
  have h5ehi := hb5.1
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
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h3, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h12, h3, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h3, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h0, h14, h3, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h17, h19, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h17, h21, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h1, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h0, h23, h3, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h27, h29, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h27, h3, h31, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h1, h33, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                          · linarith only [h0, h29, h35, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h26, h33, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h38, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                    · linarith only [h0, h3, h38, h40, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h0, h3, h38, h42, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                        · linarith only [h1, h44, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                          · linarith only [h2, h26, h46, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                            · linarith only [h3, h48, h6, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                              · linarith only [h3, h50, h6, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                                · linarith only [h0, h26, h4, h52, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                                  · linarith only [h26, h3, h38, h54, h6, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h3, h38, h54, h6, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
              · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                · linarith only [h4, h5, h58, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
                  · linarith only [h0, h60, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h5, h60, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
                · linarith only [h4, h5, h63, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h65 | h65
                  · linarith only [h0, h65, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h5, h65, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
            · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
              · linarith only [h3, h4, h69, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                  · linarith only [h0, h72, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h4, h72, hc12, hc24, hlam, hphi]
                · linarith only [h3, h4, h71, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
              · linarith only [h3, h4, h76, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h4, h79, hc12, hc24, hlam, hphi]
                · linarith only [h3, h4, h78, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h83 | h83
          · rcases m.htr 0 2 5 (by decide) (by decide) with h84 | h84
            · rcases m.htr 0 3 4 (by decide) (by decide) with h85 | h85
              · rcases m.htr 0 4 5 (by decide) (by decide) with h86 | h86
                · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                  · linarith only [h3, h84, h87, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h0, h90, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h3, h84, h90, hc12, hc23, hlam, hphi]
                    · linarith only [h3, h83, h89, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                  · linarith only [h3, h84, h94, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                      · linarith only [h1, h94, h97, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h3, h84, h97, hc12, hc23, hlam, hphi]
                    · linarith only [h3, h83, h96, hc12, hc23, hlam, hphi]
              · linarith only [h3, h83, h85, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                · linarith only [h103, h83, h84, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h105, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                      · linarith only [h0, h108, h84, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                        · linarith only [h1, h110, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h102, h110, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h107, h3, h83, hc12, hc23, hlam, hphi]
              · linarith only [h102, h3, h83, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h115 | h115
            · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
              · rcases m.htr 0 4 5 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
                  · linarith only [h115, h118, h3, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                    · linarith only [h1, h115, h118, h120, h83, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                      · linarith only [h1, h118, h122, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h115, h122, h3, hc12, hc23, hlam, hphi]
                · linarith only [h115, h117, h83, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                  · linarith only [h0, h127, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                    · linarith only [h1, h115, h127, h129, h83, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h1, h127, h131, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h115, h131, h3, hc12, hc23, hlam, hphi]
                · linarith only [h115, h116, h126, h3, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h135 | h135
              · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · linarith only [h0, h137, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · linarith only [h1, h137, h139, h83, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                      · linarith only [h0, h115, h141, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                        · linarith only [h1, h143, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h135, h143, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                  · linarith only [h0, h135, h146, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                    · linarith only [h0, h148, h83, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                      · linarith only [h0, h115, h150, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                        · linarith only [h1, h152, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h135, h152, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                  · linarith only [h0, h156, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
                    · linarith only [h0, h155, h158, h83, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
                      · linarith only [h1, h115, h156, h160, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                        · linarith only [h1, h135, h162, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                          · linarith only [h164, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h155, h162, h164, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                  · linarith only [h0, h167, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                    · linarith only [h0, h169, h83, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                      · linarith only [h0, h115, h171, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                        · linarith only [h1, h135, h173, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                          · linarith only [h155, h175, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                                  · linarith only [h1, h135, h155, h180, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h1, h135, h177, h179, h180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h1, h135, h177, h179, hc45, hlam, hphi, ht34, u3ehi1]
                              · linarith only [h1, h135, h177, h178, hc35, hlam, hphi, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                              · linarith only [h177, h185, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                                · linarith only [h1, h135, h155, h177, h187, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                                  · linarith only [h177, h187, h189, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h1, h135, h189, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h192 | h192
        · rcases m.htr 0 2 4 (by decide) (by decide) with h193 | h193
          · linarith only [h0, h193, h2, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h195 | h195
            · rcases m.htr 0 3 4 (by decide) (by decide) with h196 | h196
              · linarith only [h1, h196, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                  · linarith only [h0, h199, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h192, h193, h199, hc12, hc24, hlam, hphi]
                · linarith only [h0, h192, h198, h2, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
              · linarith only [h0, h192, h2, h203, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h205 | h205
                · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
                  · linarith only [h0, h2, h206, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h192, h195, h206, hc12, hc25, hlam, hphi]
                · linarith only [h0, h192, h2, h205, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h210 | h210
          · linarith only [h0, h2, h210, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
            · rcases m.htr 0 3 4 (by decide) (by decide) with h213 | h213
              · linarith only [h1, h2, h213, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
                  · linarith only [h0, h216, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
                    · linarith only [h1, h210, h216, h218, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                      · linarith only [h1, h2, h216, h218, h220, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h192, h212, h220, hc12, hc23, hlam, hphi]
                · linarith only [h1, h2, h215, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
              · linarith only [h1, h2, h224, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h226 | h226
                · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
                  · linarith only [h0, h192, h227, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h229 | h229
                    · linarith only [h0, h2, h210, h229, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                      · linarith only [h1, h2, h212, h227, h229, h231, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                        · linarith only [h1, h2, h229, h233, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h2, h233, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h226, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h237 | h237
      · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
        · linarith only [h0, h1, h238, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h240 | h240
          · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
            · rcases m.htr 0 3 4 (by decide) (by decide) with h242 | h242
              · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                  · linarith only [h238, h241, h244, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
                      · linarith only [h0, h1, h244, h247, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h241, h246, h247, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1, h240, h244, h246, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                  · linarith only [h0, h251, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                      · linarith only [h0, h1, h251, h254, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h241, h251, h254, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h240, h251, h253, hc12, hc23, hlam, hphi]
              · linarith only [h1, h237, h242, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 4 5 (by decide) (by decide) with h260 | h260
                · linarith only [h240, h241, h260, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                  · linarith only [h0, h1, h262, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                      · linarith only [h0, h240, h241, h259, h265, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h267 | h267
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                          · linarith only [h237, h260, h268, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                            · linarith only [h0, h1, h262, h264, h270, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h237, h262, h267, h270, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h1, h240, h259, h264, h267, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1, h240, h262, h264, hc12, hc23, hlam, hphi]
              · linarith only [h1, h237, h259, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h276 | h276
            · rcases m.htr 0 3 4 (by decide) (by decide) with h277 | h277
              · rcases m.htr 0 4 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
                  · linarith only [h0, h279, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h281 | h281
                    · linarith only [h0, h1, h240, h279, h281, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h283 | h283
                      · linarith only [h1, h237, h279, h281, h283, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h240, h276, h283, hc12, hc24, hlam, hphi]
                · linarith only [h240, h276, h278, hlam]
              · linarith only [h1, h237, h277, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
              · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
                  · linarith only [h0, h238, h290, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                    · linarith only [h0, h240, h289, h292, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                      · linarith only [h237, h276, h292, h294, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                          · linarith only [h1, h237, h290, h297, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · linarith only [h1, h237, h289, h290, h292, h297, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h237, h289, h296, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                  · linarith only [h0, h301, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
                    · linarith only [h0, h240, h303, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                      · linarith only [h0, h276, h288, h289, h305, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                          · linarith only [h237, h289, h308, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                                  · linarith only [h237, h289, h307, h313, hlam]
                                  · rcases h0bigk with h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h301, hc02, hc23, hlam, hphi, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h237, h301, h307, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p315_1, u3ehi3]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h237, h289, h301, h307, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p315_1, u3ehi3]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h238, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h240, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h276, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u0elo2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      rcases p315_3 (m.d 0 1) (by simp) with h327 | h327
                                      · linarith only [h1, h327, hlam]
                                      · linarith only [h0, h327, hlam]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h237, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p315_1, u0elo2, u3ehi3]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h237, h289, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p315_1, u0elo2, u3ehi3]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h237, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, h289, h310, h312, hc12, hc23, hlam, hphi, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h288, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h289, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h237, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p315_1, u0elo4, u3ehi3]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, h289, h310, h312, hc12, hc23, hlam, hphi, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h289, h310, h312, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p315_1, u3ehi0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h237, h289, h307, h310, h312, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p315_1, u3ehi3]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                                  · linarith only [h237, h307, h312, h343, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · rcases h0bigk with h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h0, h1, h301, hc12, hc23, hlam, hphi, p345_1]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h1, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h1, h237, h301, h307, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p345_1, u3ehi3]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h1, h301, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p345_1, u5ehi0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h0, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h238, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h240, hlam, p345_1]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h276, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p345_1, u0elo2]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      rcases p345_3 (m.d 0 1) (by simp) with h357 | h357
                                      · linarith only [h1, h357, hlam]
                                      · linarith only [h0, h357, hlam]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h237, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1, u0elo2, u3ehi3]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h237, h289, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1, u0elo2, u3ehi3]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h237, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h0, h1, h237, h301, hc12, hc23, hlam, hphi, p345_1]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h288, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h289, hlam, p345_0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h237, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1, u0elo4, u3ehi3]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      rcases p345_3 (m.d 0 1) (by simp) with h369 | h369
                                      · linarith only [h0, h1, h301, h369, hc12, hc23, hlam, hphi, p345_1]
                                      · linarith only [h0, h369, hlam]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1, u0elo4, u3ehi0]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [h237, h307, hlam, hphi, ht0b, ht34, ht45, ht5b, p345_1, u0elo4, u3ehi3]
                                    · have p345_0 := h345c.1
                                      have p345_1 := h345c.2.1
                                      have p345_2 := h345c.2.2.1
                                      have p345_3 := h345c.2.2.2
                                      linarith only [hlam, p345_0]
                              · linarith only [h1, h237, h301, h307, h311, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1, h237, h301, h307, h310, hlam]
                        · linarith only [h0, h1, h307, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h237, h288, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h379 | h379
        · linarith only [h0, h1, h379, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h381 | h381
          · linarith only [h0, h237, h381, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h383 | h383
            · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
              · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                  · linarith only [h379, h383, h386, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                    · linarith only [h0, h381, h383, h388, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
                      · linarith only [h0, h1, h386, h390, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h383, h386, h390, hc12, hc23, hlam, hphi]
                · linarith only [h0, h237, h383, h385, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                  · linarith only [h379, h383, h395, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                    · linarith only [h0, h381, h383, h397, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
                      · linarith only [h0, h1, h384, h399, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h1, h383, h384, h399, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h383, h384, h394, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h403 | h403
              · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                  · linarith only [h0, h237, h405, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                    · linarith only [h0, h381, h407, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                      · linarith only [h0, h383, h409, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h411 | h411
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                                  · linarith only [h403, h416, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                  · linarith only [h403, h404, h416, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                · linarith only [h381, h403, h404, h415, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1, h405, h414, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h237, h403, h405, h411, h413, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h237, h404, h412, hlam]
                        · linarith only [h1, h403, h411, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
                  · linarith only [h0, h424, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
                    · linarith only [h0, h237, h404, h426, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h428 | h428
                      · linarith only [h0, h237, h383, h404, h428, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                          · linarith only [h0, h237, h404, h424, h430, h431, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h237, h431, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h403, h430, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h435 | h435
                · rcases m.htr 1 2 3 (by decide) (by decide) with h436 | h436
                  · linarith only [h0, h436, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
                    · linarith only [h0, h1, h381, h403, h438, hc02, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                      · linarith only [h0, h1, h383, h403, h440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                        · linarith only [h0, h1, h403, h436, h442, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h442, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
                  · linarith only [h0, h445, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h447 | h447
                    · linarith only [h0, h1, h403, h435, h447, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                      · linarith only [h0, h1, h383, h403, h435, h449, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                        · linarith only [h0, h1, h403, h445, h451, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h451, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h454 | h454
    · rcases m.htr 0 1 4 (by decide) (by decide) with h455 | h455
      · rcases m.htr 0 2 3 (by decide) (by decide) with h456 | h456
        · rcases m.htr 0 2 4 (by decide) (by decide) with h457 | h457
          · rcases m.htr 0 2 5 (by decide) (by decide) with h458 | h458
            · rcases m.htr 0 3 4 (by decide) (by decide) with h459 | h459
              · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
                · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h462 | h462
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h463 | h463
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h464 | h464
                        · linarith only [h454, h464, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h459, h464, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h458, h463, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h454, h459, h462, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h454, h459, h461, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
                        · linarith only [h454, h473, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h459, h473, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h458, h472, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h454, h470, h471, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h470, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
                · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
                        · linarith only [h454, h459, h483, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
                          · linarith only [h0, h455, h485, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h455, h479, h480, h483, h485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h458, h482, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h454, h480, h481, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h480, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                        · linarith only [h454, h459, h494, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                          · linarith only [h455, h479, h496, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                            · linarith only [h454, h459, h491, h498, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h500 | h500
                              · linarith only [h454, h459, h491, h500, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h502 | h502
                                · linarith only [h457, h459, h479, h502, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
                                  · linarith only [h454, h459, h479, h491, h504, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h454, h459, h491, h504, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h454, h491, h493, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h454, h491, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h510 | h510
              · rcases m.htr 0 4 5 (by decide) (by decide) with h511 | h511
                · linarith only [h0, h454, h458, h510, h511, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h514 | h514
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                      · linarith only [h0, h454, h458, h513, h515, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h454, h513, h515, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h454, h513, h514, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h513, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h520 | h520
                · linarith only [h0, h455, h458, h520, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h523 | h523
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
                      · linarith only [h0, h454, h458, h522, h524, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h454, h522, h524, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h454, h522, h523, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h522, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h455, h457, hlam]
        · linarith only [h0, h454, h456, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h531 | h531
        · rcases m.htr 0 2 4 (by decide) (by decide) with h532 | h532
          · rcases m.htr 0 2 5 (by decide) (by decide) with h533 | h533
            · rcases m.htr 0 3 4 (by decide) (by decide) with h534 | h534
              · linarith only [h454, h455, h534, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
                · rcases m.htr 1 2 3 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h538 | h538
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                        · linarith only [h454, h534, h540, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h454, h455, h537, h540, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h454, h455, h533, h537, h538, h539, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h0, h454, h532, h537, h538, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h0, h454, h537, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h454, h455, h536, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h547 | h547
              · linarith only [h454, h455, h547, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h549 | h549
                · linarith only [h532, h533, h549, hlam]
                · linarith only [h454, h455, h549, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h552 | h552
            · rcases m.htr 0 3 4 (by decide) (by decide) with h553 | h553
              · linarith only [h0, h454, h532, h553, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
                · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
                    · linarith only [h0, h454, h532, h557, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h454, h556, h557, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h556, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h454, h455, h555, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h562 | h562
              · linarith only [h0, h454, h532, h562, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
                    · linarith only [h0, h454, h532, h565, h566, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h454, h565, h566, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h454, h565, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h454, h455, h564, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h454, h531, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h572 | h572
      · rcases m.htr 0 2 3 (by decide) (by decide) with h573 | h573
        · rcases m.htr 0 2 4 (by decide) (by decide) with h574 | h574
          · rcases m.htr 0 2 5 (by decide) (by decide) with h575 | h575
            · rcases m.htr 0 3 4 (by decide) (by decide) with h576 | h576
              · rcases m.htr 0 4 5 (by decide) (by decide) with h577 | h577
                · rcases m.htr 1 2 3 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h579 | h579
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h580 | h580
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h582 | h582
                          · linarith only [h572, h582, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h454, h572, h573, h577, h581, h582, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h454, h572, h577, h581, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h454, h572, h575, h577, h578, h580, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · linarith only [h454, h572, h577, h578, h579, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h572, h577, h578, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h589 | h589
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h590 | h590
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h591 | h591
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h592 | h592
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                          · linarith only [h572, h577, h593, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                            · linarith only [h573, h595, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h573, h576, h595, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                        · linarith only [h454, h572, h576, h577, h592, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h575, h591, hlam]
                    · linarith only [h0, h574, h590, hlam]
                  · linarith only [h0, h573, h589, hlam]
              · linarith only [h454, h572, h576, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h603 | h603
              · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
                · linarith only [h0, h572, h575, h604, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                      · linarith only [h573, h575, h608, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                        · linarith only [h0, h572, h608, h610, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h454, h573, h603, h610, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h574, h575, h607, hc12, hc25, hlam, hphi]
                  · linarith only [h0, h572, h573, h603, h606, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
              · linarith only [h454, h572, h603, hlam]
          · linarith only [h0, h572, h574, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h617 | h617
          · rcases m.htr 0 2 5 (by decide) (by decide) with h618 | h618
            · rcases m.htr 0 3 4 (by decide) (by decide) with h619 | h619
              · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                  · linarith only [h573, h618, h621, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h572, h620, h621, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
                  · linarith only [h573, h618, h624, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                        · linarith only [h0, h572, h624, h628, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h619, h620, h628, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h0, h618, h627, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h572, h617, h619, h626, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
              · linarith only [h0, h572, h573, h619, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h634 | h634
              · rcases m.htr 0 4 5 (by decide) (by decide) with h635 | h635
                · linarith only [h0, h572, h618, h635, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h639 | h639
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                        · linarith only [h0, h572, h573, h637, h640, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h573, h634, h637, h640, hlam]
                      · linarith only [h0, h572, h573, h634, h637, h639, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h572, h573, h634, h637, h638, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                      · linarith only [h0, h572, h618, h634, h637, h646, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                        · linarith only [h0, h572, h637, h648, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h634, h635, h648, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h617, h645, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h572, h573, h634, hlam]
          · linarith only [h0, h572, h617, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h654 | h654
        · rcases m.htr 0 2 4 (by decide) (by decide) with h655 | h655
          · rcases m.htr 0 2 5 (by decide) (by decide) with h656 | h656
            · rcases m.htr 0 3 4 (by decide) (by decide) with h657 | h657
              · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                            · linarith only [h654, h664, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h654, h657, h664, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                          · linarith only [h572, h654, h657, h658, h663, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h454, h657, h662, hlam]
                      · linarith only [h0, h656, h661, hlam]
                    · linarith only [h0, h655, h660, hlam]
                  · linarith only [h0, h654, h659, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h673 | h673
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h675 | h675
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h676 | h676
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                            · linarith only [h654, h677, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h657, h658, h675, h676, h677, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h680 | h680
                            · linarith only [h654, h680, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h572, h657, h676, h680, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h454, h657, h675, hlam]
                      · linarith only [h0, h656, h674, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h655, h673, hlam]
                  · linarith only [h0, h654, h672, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
                · rcases m.htr 1 2 3 (by decide) (by decide) with h688 | h688
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h689 | h689
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h690 | h690
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h691 | h691
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h693 | h693
                            · linarith only [h654, h657, h693, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                              · linarith only [h654, h657, h688, h691, h695, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h697 | h697
                                · linarith only [h655, h697, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                · linarith only [h687, h693, h697, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                          · linarith only [h657, h687, h691, h692, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h701 | h701
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h702 | h702
                            · linarith only [h454, h691, h702, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h704 | h704
                              · linarith only [h454, h654, h691, h704, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h706 | h706
                                · linarith only [h655, h706, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                · linarith only [h655, h687, h702, h706, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                          · linarith only [h572, h655, h687, h701, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h656, h690, hlam]
                    · linarith only [h0, h655, h689, hlam]
                  · linarith only [h0, h654, h688, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h713 | h713
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h714 | h714
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h715 | h715
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h716 | h716
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h718 | h718
                            · linarith only [h654, h657, h718, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h720 | h720
                              · linarith only [h655, h718, h720, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h722 | h722
                                · linarith only [h655, h687, h722, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                                  · linarith only [h655, h687, h718, h724, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h657, h713, h716, h717, h724, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h654, h657, h716, h717, hc45, hlam, hphi, ht34, u3ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                          · linarith only [h654, h657, h687, h716, h728, hc34, hlam, hphi, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h730 | h730
                            · linarith only [h454, h654, h716, h728, h730, hc45, hlam, hphi, ht34, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h732 | h732
                              · linarith only [h655, h730, h732, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h734 | h734
                                · linarith only [h454, h655, h716, h728, h734, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h736 | h736
                                  · linarith only [h454, h716, h728, h736, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h654, h657, h736, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h656, h715, hlam]
                    · linarith only [h0, h654, h655, h714, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h0, h654, h713, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h742 | h742
              · rcases m.htr 0 4 5 (by decide) (by decide) with h743 | h743
                · linarith only [h655, h656, h743, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h746 | h746
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                      · linarith only [h654, h656, h742, h747, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h749 | h749
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
                          · linarith only [h572, h743, h746, h747, h750, hc01, hc25, hlam, hphi, ht12]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                            · linarith only [h654, h752, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h742, h752, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                        · linarith only [h454, h742, h749, hlam]
                    · linarith only [h0, h655, h746, hlam]
                  · linarith only [h0, h654, h745, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
                · linarith only [h655, h656, h758, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                      · linarith only [h654, h656, h762, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
                        · linarith only [h742, h760, h762, h764, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h766 | h766
                          · linarith only [h572, h758, h761, h762, h766, hc01, hc25, hlam, hphi, ht12]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h768 | h768
                            · linarith only [h654, h768, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h770 | h770
                              · linarith only [h0, h655, h762, h768, h770, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                              · linarith only [h0, h655, h762, h768, h770, hc35, hlam, hphi, u3ehi2]
                    · linarith only [h0, h655, h761, hlam]
                  · linarith only [h0, h654, h760, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h775 | h775
            · rcases m.htr 0 3 4 (by decide) (by decide) with h776 | h776
              · linarith only [h654, h655, h776, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
                · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h780 | h780
                    · linarith only [h655, h775, h780, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h782 | h782
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h783 | h783
                        · linarith only [h776, h779, h780, h783, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
                            · linarith only [h654, h783, h786, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                            · linarith only [h0, h654, h780, h786, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h572, h778, h785, hlam]
                      · linarith only [h0, h775, h782, hlam]
                  · linarith only [h0, h654, h779, hlam]
                · linarith only [h654, h655, h778, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h793 | h793
              · linarith only [h654, h655, h793, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h795 | h795
                · rcases m.htr 1 2 3 (by decide) (by decide) with h796 | h796
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h797 | h797
                    · linarith only [h654, h655, h797, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h799 | h799
                      · linarith only [h654, h775, h797, h799, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h801 | h801
                        · linarith only [h793, h796, h797, h801, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h803 | h803
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h804 | h804
                            · linarith only [h654, h801, h804, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                            · linarith only [h0, h654, h797, h804, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h572, h654, h655, h803, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h654, h796, hlam]
                · linarith only [h654, h655, h795, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h810 | h810
          · rcases m.htr 0 2 5 (by decide) (by decide) with h811 | h811
            · rcases m.htr 0 3 4 (by decide) (by decide) with h812 | h812
              · rcases m.htr 0 4 5 (by decide) (by decide) with h813 | h813
                · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                  · linarith only [h654, h811, h814, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h817 | h817
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h818 | h818
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h819 | h819
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h820 | h820
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h821 | h821
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h822 | h822
                                · linarith only [h810, h822, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                                · linarith only [h0, h810, h813, h814, h820, h822, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h810, h813, h814, h821, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h0, h810, h813, h814, h820, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h572, h813, h819, hlam]
                        · linarith only [h454, h812, h818, hlam]
                      · linarith only [h0, h811, h817, hlam]
                    · linarith only [h0, h810, h816, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
                  · linarith only [h654, h811, h831, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h833 | h833
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h834 | h834
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h835 | h835
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h836 | h836
                          · linarith only [h812, h813, h831, h833, h836, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h838 | h838
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h839 | h839
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h840 | h840
                                · linarith only [h810, h836, h840, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                                  · linarith only [h572, h836, h842, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases h0bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, hlam, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h454, hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h572, hlam, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p844_1, u0elo0, u5ehi0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, h831, hc01, hc23, hlam, hphi, ht12, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h654, hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, h572, h831, hc01, hc23, hlam, hphi, ht12, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, h831, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p844_1, u5ehi0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      rcases p844_3 (m.d 0 1) (by simp) with h855 | h855
                                      · linarith only [h454, h855, hlam]
                                      · rcases p844_3 (m.d 0 2) (by simp) with h857 | h857
                                        · linarith only [h654, h857, hlam]
                                        · linarith only [h0, h857, hlam]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h811, h840, hc24, hlam, hphi, ht0b, ht45, ht5b, p844_1, u0elo2]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h810, h838, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo2, u3ehi3]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h810, h813, h838, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo2, u3ehi3]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h572, h836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h810, hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h812, hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h813, hlam, p844_0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, h811, h831, hc01, hc23, hlam, hphi, ht12, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h811, hlam, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, h811, h831, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u3ehi0]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [h0, h572, h811, h831, hc01, hc23, hlam, hphi, ht12, p844_1]
                                    · have p844_0 := h844c.1
                                      have p844_1 := h844c.2.1
                                      have p844_2 := h844c.2.2.1
                                      have p844_3 := h844c.2.2.2
                                      linarith only [hlam, p844_0]
                              · linarith only [h0, h811, h831, h839, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h0, h812, h831, h838, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h454, h812, h813, h835, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h811, h834, hlam]
                    · linarith only [h0, h810, h833, hlam]
              · linarith only [h654, h810, h812, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h880 | h880
              · rcases m.htr 0 4 5 (by decide) (by decide) with h881 | h881
                · linarith only [h810, h811, h881, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h883 | h883
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h884 | h884
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h885 | h885
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h888 | h888
                            · linarith only [h654, h810, h883, h888, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h654, h880, h888, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h891 | h891
                            · linarith only [h654, h810, h883, h891, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h654, h880, h891, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h880, h886, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h572, h654, h810, h883, h885, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h654, h810, h880, h883, h884, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h897 | h897
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h898 | h898
                      · linarith only [h811, h883, h898, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                          · linarith only [h880, h881, h883, h897, h901, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h903 | h903
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h904 | h904
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h905 | h905
                                · linarith only [h572, h810, h901, h905, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h0, h810, h898, h903, h905, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h654, h810, h903, h904, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h0, h883, h903, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h454, h572, h880, h883, h897, h900, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h810, h897, hlam]
              · linarith only [h654, h810, h880, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h913 | h913
            · rcases m.htr 0 3 4 (by decide) (by decide) with h914 | h914
              · rcases m.htr 0 4 5 (by decide) (by decide) with h915 | h915
                · rcases m.htr 1 2 3 (by decide) (by decide) with h916 | h916
                  · linarith only [h654, h913, h916, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h918 | h918
                    · linarith only [h810, h913, h916, h918, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h920 | h920
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h921 | h921
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h922 | h922
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h923 | h923
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h924 | h924
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h925 | h925
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                                  · linarith only [h914, h926, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                  · linarith only [h915, h926, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                · linarith only [h0, h914, h915, h918, h925, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h913, h918, h923, h924, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h914, h923, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h572, h914, h915, h922, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h454, h914, h921, hlam]
                      · linarith only [h0, h913, h920, hlam]
                · linarith only [h810, h913, h915, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h936 | h936
                · rcases m.htr 1 2 3 (by decide) (by decide) with h937 | h937
                  · linarith only [h654, h913, h937, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h939 | h939
                    · linarith only [h810, h913, h939, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                        · linarith only [h654, h913, h914, h937, h942, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h944 | h944
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h945 | h945
                            · linarith only [h0, h937, h942, h945, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h654, h913, h945, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h913, h936, h937, h942, h944, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi2]
                      · linarith only [h0, h913, h941, hlam]
                · linarith only [h810, h913, h936, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h951 | h951
              · rcases m.htr 0 4 5 (by decide) (by decide) with h952 | h952
                · rcases m.htr 1 2 3 (by decide) (by decide) with h953 | h953
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h954 | h954
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h955 | h955
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h956 | h956
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h957 | h957
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h958 | h958
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h960 | h960
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h961 | h961
                                  · linarith only [h951, h961, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                  · linarith only [h952, h961, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                · linarith only [h810, h952, h960, hlam]
                              · linarith only [h654, h951, h959, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h654, h951, h958, hlam]
                          · linarith only [h810, h952, h954, h957, hlam]
                        · linarith only [h654, h951, h953, h956, hlam]
                      · linarith only [h654, h951, h953, h955, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h654, h951, h953, h954, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h971 | h971
                    · linarith only [h0, h810, h953, h971, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
                      · linarith only [h0, h913, h953, h973, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h975 | h975
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h976 | h976
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h977 | h977
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h978 | h978
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h979 | h979
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h980 | h980
                                  · linarith only [h951, h980, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                  · linarith only [h952, h980, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                                · linarith only [h0, h810, h951, h952, h979, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h654, h951, h978, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h454, h951, h953, h977, hlam]
                          · linarith only [h572, h952, h976, hlam]
                        · linarith only [h454, h951, h975, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h988 | h988
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h989 | h989
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h990 | h990
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h991 | h991
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h992 | h992
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h994 | h994
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h995 | h995
                                · linarith only [h951, h952, h988, h993, h995, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h810, h991, h992, h995, hc01, hc13, hlam, hphi]
                              · linarith only [h654, h951, h994, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h654, h951, h993, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1000 | h1000
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1001 | h1001
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1002 | h1002
                                · linarith only [h1002, h572, h992, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1004 | h1004
                                  · linarith only [h0, h1004, h810, h951, h989, h992, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases h0bigk with h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h454, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h572, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p1006_1, u0elo0, u5ehi0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h1000, h810, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h654, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h810, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h913, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h654, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h654, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h572, h654, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h654, h988, hc12, hlam, hphi, ht01, ht0b, ht5b, p1006_1, u5ehi0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h572, h992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h810, h989, h992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h951, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h952, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h1001, h913, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h1001, h913, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h1001, h913, h988, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1006_1, u3ehi0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h1001, h572, h913, h988, hc01, hc12, hlam, hphi, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                              · linarith only [h1001, h654, h951, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1000, h654, h951, hlam]
                        · linarith only [h951, h991, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h654, h951, h988, h990, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h654, h951, h988, h989, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1037 | h1037
                    · linarith only [h0, h1037, h810, h988, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1039 | h1039
                      · linarith only [h0, h1039, h913, h988, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1042 | h1042
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1043 | h1043
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1044 | h1044
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1045 | h1045
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1046 | h1046
                                  · linarith only [h1046, h951, h952, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                  · rcases h0bigk with h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h0, hlam, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h454, hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h572, hlam, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p1048_1, u0elo0, u5ehi0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h0, h1039, hc01, hc25, hlam, hphi, ht12, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h654, hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h810, hlam, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h913, hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      rcases p1048_3 (m.d 0 1) (by simp) with h1059 | h1059
                                      · linarith only [h1059, h454, hlam]
                                      · rcases p1048_3 (m.d 0 2) (by simp) with h1061 | h1061
                                        · linarith only [h1061, h654, hlam]
                                        · linarith only [h0, h1061, hlam]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      rcases p1048_3 (m.d 0 1) (by simp) with h1064 | h1064
                                      · linarith only [h1064, h454, hlam]
                                      · rcases p1048_3 (m.d 0 2) (by simp) with h1066 | h1066
                                        · linarith only [h1066, h654, hlam]
                                        · rcases p1048_3 (m.d 0 3) (by simp) with h1068 | h1068
                                          · rcases p1048_3 (m.d 0 4) (by simp) with h1069 | h1069
                                            · linarith only [h1069, h951, hlam]
                                            · linarith only [h1069, h810, hlam]
                                          · linarith only [h1068, h654, hlam]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h951, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u0elo2, u3ehi3]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h951, h952, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u0elo2, u3ehi3]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h1041, h1042, h952, hc01, hc13, hlam, hphi, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h1041, h1042, h952, h988, hc02, hc23, hlam, hphi, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h951, hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h952, hlam, p1048_0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h1041, h1042, h952, h988, hc01, hc23, hlam, hphi, ht12, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h0, h1041, h1042, h952, h988, hc01, hc23, hlam, hphi, ht12, p1048_1]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h1041, h1042, h952, h988, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1048_1, u3ehi0]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [h1041, h1042, h951, h952, h988, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1048_1, u3ehi3]
                                    · have p1048_0 := h1048c.1
                                      have p1048_1 := h1048c.2.1
                                      have p1048_2 := h1048c.2.2.1
                                      have p1048_3 := h1048c.2.2.2
                                      linarith only [hlam, p1048_0]
                                · linarith only [h0, h1041, h1042, h1045, h810, h988, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h1044, h454, h951, h988, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1041, h1042, h1043, h951, h952, h988, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1089 | h1089
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1090 | h1090
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1091 | h1091
                                · linarith only [h0, h1037, h1042, h1089, h1091, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h0, h1037, h1091, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h1090, h454, h951, h988, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1089, h454, h951, h988, hlam]
                        · linarith only [h1041, h454, h951, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1097 | h1097
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1098 | h1098
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1100 | h1100
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1101 | h1101
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1102 | h1102
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1103 | h1103
                            · linarith only [h1098, h1103, h951, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h0, h1101, h1103, h654, hc01, hc13, hlam, hphi]
                          · linarith only [h1097, h1101, h1102, h951, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1107 | h1107
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1108 | h1108
                            · linarith only [h1101, h1108, h454, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
                              · linarith only [h1098, h1101, h1110, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
                                  · rcases h0bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h0, hlam, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h454, hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h572, hlam, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p1114_1, u0elo0, u5ehi0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1098, h1101, h654, hc01, hc34, hlam, hphi, ht12, ht23, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h654, hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h810, hlam, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h913, hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1101, h454, hc01, hc34, hlam, hphi, ht12, ht23, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1098, h1101, h654, hc02, hc34, hlam, hphi, ht23, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h951, hlam, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1098, h1101, h654, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1114_1, u5ehi0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1099, h810, hc01, hc12, hlam, hphi, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h0, h1099, h810, hc01, hc12, hlam, hphi, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1099, h810, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1114_1, u3ehi0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [hlam, p1114_0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1099, h810, hc12, hlam, hphi, ht01, ht0b, ht5b, p1114_1, u5ehi0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1097, h1099, h810, hc01, hc12, hlam, hphi, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h0, h1097, h1099, h810, hc01, hc12, hlam, hphi, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1097, h1099, h810, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1114_1, u3ehi0]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [h1097, hlam, p1114_1]
                                    · have p1114_0 := h1114c.1
                                      have p1114_1 := h1114c.2.1
                                      have p1114_2 := h1114c.2.2.1
                                      have p1114_3 := h1114c.2.2.2
                                      linarith only [hlam, p1114_0]
                                  · linarith only [h1101, h1113, hc45, hlam, hphi, ht34, u3ehi1]
                                · linarith only [h1097, h1112, h810, hlam]
                          · linarith only [h1097, h1099, h1107, h572, h810, hc01, hc12, hlam, hphi]
                      · linarith only [h1097, h1099, h1100, h810, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h1098, h1099, h654, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1145 | h1145
                    · linarith only [h0, h1098, h1145, h810, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1147 | h1147
                      · linarith only [h0, h1098, h1147, h913, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1149 | h1149
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1150 | h1150
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1151 | h1151
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1152 | h1152
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1153 | h1153
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1154 | h1154
                                  · rcases h0bigk with h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h454, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h572, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1097, hlam, hphi, ht0b, ht5b, p1155_1, u0elo0, u5ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, h1147, h1151, h1153, hc01, hc23, hlam, hphi, ht12, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h654, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h810, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h913, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1149, h951, hc01, hc13, hlam, hphi, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1149, h951, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h951, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1097, h1098, h1149, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1155_1, u5ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1098, h1149, h951, hc01, hc23, hlam, hphi, ht12, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, h1098, h1149, h951, hc01, hc23, hlam, hphi, ht12, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1098, h1149, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1155_1, u3ehi0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1097, h1098, h1149, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1155_1, u5ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1097, h1098, h1149, h951, hc01, hc23, hlam, hphi, ht12, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, h1097, h1098, h1149, h951, hc01, hc23, hlam, hphi, ht12, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1097, h1098, h1149, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1155_1, u3ehi0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1097, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                  · linarith only [h1154, h951, hc45, hlam, hphi, ht34, u3ehi0]
                                · linarith only [h0, h1097, h1098, h1149, h1153, h810, h951, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h1098, h1149, h1152, h951, hc35, hlam, hphi, u3ehi0]
                            · linarith only [h1098, h1149, h1151, hlam]
                          · linarith only [h1097, h1149, h1150, h951, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1186 | h1186
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1187 | h1187
                            · linarith only [h1149, h1187, h454, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1098, h1187, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1097, h1186, h572, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1191 | h1191
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1192 | h1192
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1194 | h1194
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1195 | h1195
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1196 | h1196
                            · linarith only [h1191, h1196, h951, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h0, h1191, h1194, h1196, h654, hc01, hc12, hlam, hphi]
                          · linarith only [h1194, h1195, h951, hc45, hlam, hphi, ht34, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1200 | h1200
                          · linarith only [h1097, h1194, h1200, h951, hc34, hlam, hphi, u3ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1202 | h1202
                            · linarith only [h1191, h1194, h1200, h1202, hc45, hlam, hphi, ht34, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
                              · linarith only [h1191, h1194, h1200, h1204, hc45, hlam, hphi, ht34, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
                                · linarith only [h0, h1191, h1194, h1200, h1206, h654, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1208 | h1208
                                  · linarith only [h0, h1191, h1194, h1200, h1208, h654, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h1208, h951, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h1191, h1193, h654, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1191, h1192, h654, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1213 | h1213
                    · linarith only [h0, h1191, h1213, h810, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1215 | h1215
                      · linarith only [h0, h1191, h1215, h913, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1217 | h1217
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1218 | h1218
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1219 | h1219
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1220 | h1220
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1221 | h1221
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1222 | h1222
                                  · linarith only [h1097, h1222, h951, hc34, hlam, hphi, u3ehi0]
                                  · linarith only [h1218, h1222, h951, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · linarith only [h1213, h1218, h1221, hlam]
                              · linarith only [h1097, h1213, h1218, h1219, h1220, h951, hc35, hlam, hphi, u3ehi0]
                            · linarith only [h1097, h1191, h1217, h1218, h1219, h951, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h1217, h1218, h951, hc45, hlam, hphi, ht34, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1229 | h1229
                          · linarith only [h1097, h1217, h1229, h951, hc34, hlam, hphi, u3ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1231 | h1231
                            · linarith only [h0, h1191, h1217, h1231, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1191, h1231, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
