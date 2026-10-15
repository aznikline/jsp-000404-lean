import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_LI_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                      · linarith only [h0, h10, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h0, h10, h14, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h10, h16, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                            · linarith only [h0, h16, h4, h7, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h19, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                        · linarith only [h0, h19, h21, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h0, h19, h23, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                            · linarith only [h1, h25, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                            · linarith only [h0, h25, h4, h7, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h29, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                      · linarith only [h0, h32, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                          · linarith only [h0, h32, h36, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                            · linarith only [h38, h7, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h29, h40, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h0, h34, h42, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                                · linarith only [h0, h31, h38, h42, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                      · linarith only [h0, h45, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                        · linarith only [h4, h45, h47, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                          · linarith only [h0, h4, h45, h49, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                            · linarith only [h1, h51, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                              · linarith only [h29, h53, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                                · linarith only [h0, h31, h47, h5, h55, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                                  · linarith only [h4, h57, h7, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                                    · linarith only [h0, h31, h4, h45, h5, h59, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                                      · linarith only [h31, h4, h45, h61, h7, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h4, h45, h61, h7, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h64 | h64
                · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h4, h6, h65, hlam]
                  · linarith only [h64, h65, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h68 | h68
                  · linarith only [h64, h68, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h5, h6, h70, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                      · linarith only [h0, h72, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · linarith only [h4, h6, h72, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
                · linarith only [h4, h5, h76, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h78 | h78
                  · linarith only [h76, h78, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h80 | h80
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h81, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · linarith only [h4, h5, h81, hc12, hc24, hlam, hphi]
                    · linarith only [h4, h5, h80, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h85 | h85
                · linarith only [h4, h5, h85, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h87 | h87
                  · linarith only [h85, h87, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                      · linarith only [h0, h90, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · linarith only [h4, h5, h90, hc12, hc24, hlam, hphi]
                    · linarith only [h4, h5, h89, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
            · rcases m.htr 0 2 5 (by decide) (by decide) with h95 | h95
              · rcases m.htr 0 3 4 (by decide) (by decide) with h96 | h96
                · rcases m.htr 0 3 5 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                      · linarith only [h4, h94, h98, h99, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                        · linarith only [h0, h101, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · linarith only [h101, h4, h94, hc12, hc23, hlam, hphi]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                      · linarith only [h104, h4, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                        · linarith only [h1, h104, h106, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · linarith only [h106, h4, h94, hc12, hc23, hlam, hphi]
                  · linarith only [h96, h97, hc35, hlam, hphi, u3ehi3]
                · linarith only [h4, h94, h96, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                    · linarith only [h113, h94, h95, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h115, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                        · linarith only [h1, h115, h117, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · linarith only [h117, h4, h94, hc12, hc23, hlam, hphi]
                  · linarith only [h111, h112, hc35, hlam, hphi, u3ehi3]
                · linarith only [h111, h4, h94, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                      · linarith only [h122, h126, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                        · linarith only [h0, h128, h94, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                            · linarith only [h1, h131, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                            · linarith only [h123, h131, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h122, h130, h94, hc12, hc24, hlam, hphi]
                    · linarith only [h122, h125, h94, hlam]
                  · linarith only [h123, h124, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
                  · linarith only [h123, h137, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h122, h137, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
                · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                      · linarith only [h0, h143, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                        · linarith only [h0, h145, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                          · linarith only [h0, h122, h147, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                            · linarith only [h1, h149, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                            · linarith only [h140, h149, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                      · linarith only [h0, h140, h152, h4, h94, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
                        · linarith only [h0, h154, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                          · linarith only [h1, h122, h152, h156, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                            · linarith only [h1, h158, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                            · linarith only [h140, h158, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h140, h141, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h140, h162, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                      · linarith only [h0, h165, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                        · linarith only [h0, h164, h167, h4, h94, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                          · linarith only [h1, h122, h165, h169, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                            · linarith only [h1, h140, h171, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                              · linarith only [h1, h162, h173, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                                · linarith only [h175, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                                · linarith only [h164, h175, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h178, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                        · linarith only [h1, h178, h180, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                          · linarith only [h0, h122, h182, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                            · linarith only [h1, h140, h184, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                              · linarith only [h1, h140, h186, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                                · linarith only [h140, h164, h188, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h192 | h192
                                      · linarith only [h1, h140, h164, h192, hc34, hlam, hphi, u3ehi1]
                                      · linarith only [h1, h140, h192, hc45, hlam, hphi, ht34, u3ehi1]
                                    · linarith only [h1, h140, h190, h191, hc45, hlam, hphi, ht34, u3ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                                    · linarith only [h1, h140, h164, h190, h196, hc34, hlam, hphi, u3ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                                      · linarith only [h0, h196, h198, h94, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h1, h140, h198, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h203 | h203
      · linarith only [h1, h203, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h205 | h205
        · rcases m.htr 0 2 3 (by decide) (by decide) with h206 | h206
          · linarith only [h0, h1, h206, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h208 | h208
            · linarith only [h0, h1, h208, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h210 | h210
              · rcases m.htr 0 3 4 (by decide) (by decide) with h211 | h211
                · rcases m.htr 0 3 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
                      · linarith only [h206, h210, h214, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
                        · linarith only [h0, h1, h208, h210, h212, h216, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                          · linarith only [h0, h1, h218, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · linarith only [h0, h1, h210, h218, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h203, h205, h213, hlam]
                  · linarith only [h211, h212, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h223 | h223
                  · linarith only [h211, h223, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h1, h210, h223, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h226 | h226
                · rcases m.htr 0 3 5 (by decide) (by decide) with h227 | h227
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
                      · linarith only [h0, h1, h206, h229, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                        · linarith only [h0, h208, h228, h231, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                          · linarith only [h0, h1, h210, h233, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                              · linarith only [h203, h205, h235, h236, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                              · linarith only [h0, h203, h235, h236, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h226, h235, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h203, h205, h228, hlam]
                  · linarith only [h226, h227, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h242 | h242
                  · linarith only [h226, h242, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h205, h242, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h245 | h245
          · linarith only [h0, h203, h245, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h247 | h247
            · linarith only [h0, h203, h247, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
              · linarith only [h0, h205, h249, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h251 | h251
                · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                      · linarith only [h0, h203, h245, h254, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                        · linarith only [h0, h247, h253, h256, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                          · linarith only [h0, h203, h249, h258, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h262 | h262
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h264 | h264
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h265 | h265
                                      · linarith only [h251, h265, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                      · linarith only [h253, h265, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                    · linarith only [h203, h253, h256, h264, hlam]
                                  · linarith only [h0, h205, h254, h260, h262, h263, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h203, h253, h262, hlam]
                              · linarith only [h0, h203, h260, h261, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h251, h260, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
                      · linarith only [h0, h273, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
                        · linarith only [h0, h205, h275, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                          · linarith only [h0, h205, h277, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                                · linarith only [h253, h279, h281, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                                · linarith only [h0, h203, h281, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1, h252, h280, hlam]
                            · linarith only [h1, h251, h279, hlam]
                  · linarith only [h251, h252, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h287 | h287
                  · linarith only [h251, h287, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
                      · linarith only [h0, h290, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h292 | h292
                        · linarith only [h0, h203, h292, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                          · linarith only [h0, h203, h294, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                            · linarith only [h1, h251, h296, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h1, h296, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                      · linarith only [h0, h299, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
                        · linarith only [h0, h301, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                          · linarith only [h0, h1, h303, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                            · linarith only [h251, h305, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · linarith only [h0, h1, h305, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h308 | h308
    · linarith only [h0, h308, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h310 | h310
      · linarith only [h0, h310, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h312 | h312
        · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
          · rcases m.htr 0 2 4 (by decide) (by decide) with h314 | h314
            · rcases m.htr 0 2 5 (by decide) (by decide) with h315 | h315
              · rcases m.htr 0 3 4 (by decide) (by decide) with h316 | h316
                · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h321 | h321
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
                              · linarith only [h310, h312, h319, h322, h323, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                              · linarith only [h308, h316, h323, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h308, h316, h322, hlam]
                          · linarith only [h0, h315, h321, hlam]
                        · linarith only [h0, h314, h320, hlam]
                      · linarith only [h0, h313, h319, hlam]
                    · linarith only [h310, h312, h318, hlam]
                  · linarith only [h316, h317, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h316, h332, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h308, h312, h332, hlam]
              · linarith only [h0, h312, h313, h315, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h336 | h336
              · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
                · linarith only [h313, h314, h337, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                  · linarith only [h337, h339, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h308, h312, h339, hlam]
              · linarith only [h0, h312, h336, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h343 | h343
            · rcases m.htr 0 2 5 (by decide) (by decide) with h344 | h344
              · rcases m.htr 0 3 4 (by decide) (by decide) with h345 | h345
                · rcases m.htr 0 3 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h347 | h347
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h348 | h348
                      · linarith only [h313, h343, h347, h348, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                              · linarith only [h310, h312, h348, h350, h353, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h308, h345, h353, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h310, h312, h345, h346, h348, h350, h352, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                          · linarith only [h310, h312, h344, h346, h350, h351, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                        · linarith only [h0, h343, h350, hlam]
                    · linarith only [h310, h312, h347, hlam]
                  · linarith only [h345, h346, hc35, hlam, hphi, u3ehi3]
                · linarith only [h313, h343, h345, hlam]
              · linarith only [h0, h312, h343, h344, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h363 | h363
              · rcases m.htr 0 3 4 (by decide) (by decide) with h364 | h364
                · rcases m.htr 0 3 5 (by decide) (by decide) with h365 | h365
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                      · linarith only [h0, h312, h313, h365, h367, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h369 | h369
                        · linarith only [h0, h312, h343, h365, h367, h369, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
                              · linarith only [h0, h312, h369, h372, h373, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                              · linarith only [h0, h312, h365, h369, h372, h373, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                            · linarith only [h0, h312, h364, h365, h367, h372, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                          · linarith only [h0, h312, h363, h365, h371, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                    · linarith only [h0, h312, h343, h366, hlam]
                  · linarith only [h364, h365, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h380 | h380
                  · linarith only [h364, h380, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h312, h313, h380, hlam]
              · linarith only [h0, h312, h363, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h384 | h384
          · rcases m.htr 0 2 4 (by decide) (by decide) with h385 | h385
            · rcases m.htr 0 2 5 (by decide) (by decide) with h386 | h386
              · rcases m.htr 0 3 4 (by decide) (by decide) with h387 | h387
                · rcases m.htr 0 3 5 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                                  · linarith only [h384, h396, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                  · linarith only [h387, h396, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                                · linarith only [h308, h387, h389, h390, h395, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                              · linarith only [h308, h387, h388, h394, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi3]
                            · linarith only [h308, h384, h387, h393, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h386, h392, hlam]
                        · linarith only [h0, h385, h391, hlam]
                      · linarith only [h0, h384, h390, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                                · linarith only [h389, h410, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                                  · linarith only [h384, h412, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                  · linarith only [h387, h412, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h0, h384, h388, h409, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                            · linarith only [h308, h387, h408, hlam]
                          · linarith only [h0, h386, h407, hlam]
                        · linarith only [h0, h385, h406, hlam]
                      · linarith only [h0, h384, h405, hlam]
                  · linarith only [h387, h388, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h421 | h421
                  · linarith only [h387, h421, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h425 | h425
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h426 | h426
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h427 | h427
                            · linarith only [h387, h427, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h429 | h429
                              · linarith only [h427, h429, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
                                  · linarith only [h384, h427, h432, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                                    · linarith only [h0, h385, h434, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                                    · linarith only [h0, h385, h423, h432, h434, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                                · linarith only [h0, h385, h423, h431, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                          · linarith only [h0, h386, h426, hlam]
                        · linarith only [h0, h385, h425, hlam]
                      · linarith only [h0, h384, h424, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                            · linarith only [h387, h444, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                              · linarith only [h444, h446, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                                · linarith only [h423, h442, h448, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                                  · linarith only [h384, h450, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                                    · linarith only [h0, h308, h385, h444, h448, h452, hc01, hlam, hphi, u1elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                                      · linarith only [h308, h444, h448, h454, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · linarith only [h384, h387, h454, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h0, h386, h443, hlam]
                        · linarith only [h0, h385, h442, hlam]
                      · linarith only [h0, h384, h385, h441, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h460 | h460
                · rcases m.htr 0 3 5 (by decide) (by decide) with h461 | h461
                  · linarith only [h384, h386, h461, hlam]
                  · linarith only [h460, h461, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h464 | h464
                  · linarith only [h460, h464, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h466 | h466
                    · linarith only [h385, h386, h466, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                          · linarith only [h0, h386, h470, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                            · linarith only [h460, h468, h470, h472, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
                              · linarith only [h384, h386, h464, h472, h474, hc34, hlam, hphi, u3ehi2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                                · linarith only [h466, h476, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h478 | h478
                                  · linarith only [h384, h478, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h480 | h480
                                    · linarith only [h0, h308, h385, h470, h472, h476, h480, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                                    · linarith only [h0, h385, h470, h478, h480, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h385, h469, hlam]
                      · linarith only [h0, h384, h468, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
              · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
                · linarith only [h384, h385, h486, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
                  · linarith only [h486, h488, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                        · linarith only [h385, h485, h488, h492, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h494 | h494
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h495 | h495
                            · linarith only [h384, h385, h486, h491, h492, h495, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h497 | h497
                              · linarith only [h384, h488, h495, h497, hc34, hlam, hphi, u3ehi2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h499 | h499
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
                                  · linarith only [h384, h495, h500, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                                  · linarith only [h0, h384, h492, h500, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h310, h490, h499, hlam]
                          · linarith only [h0, h485, h494, hlam]
                      · linarith only [h0, h384, h491, hlam]
                    · linarith only [h384, h385, h490, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h507 | h507
                · linarith only [h384, h385, h507, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h509 | h509
                  · linarith only [h507, h509, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h511 | h511
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
                        · linarith only [h384, h385, h513, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                          · linarith only [h384, h485, h513, h515, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h517 | h517
                            · linarith only [h384, h485, h507, h511, h512, h513, h517, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
                              · linarith only [h384, h485, h509, h517, h519, hc34, hlam, hphi, u3ehi2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                                  · linarith only [h384, h517, h522, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                                  · linarith only [h384, h385, h522, hc34, hlam, hphi, u3ehi2]
                                · linarith only [h310, h511, h521, hlam]
                      · linarith only [h0, h384, h512, hlam]
                    · linarith only [h384, h385, h511, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h528 | h528
            · rcases m.htr 0 2 5 (by decide) (by decide) with h529 | h529
              · rcases m.htr 0 3 4 (by decide) (by decide) with h530 | h530
                · rcases m.htr 0 3 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                      · linarith only [h384, h528, h533, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h536 | h536
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h537 | h537
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h538 | h538
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h539 | h539
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h540 | h540
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                                    · linarith only [h528, h541, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                    · linarith only [h308, h384, h528, h532, h541, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
                                  · linarith only [h0, h533, h540, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h308, h384, h528, h532, h539, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
                              · linarith only [h308, h531, h538, hlam]
                            · linarith only [h308, h530, h537, hlam]
                          · linarith only [h0, h529, h536, hlam]
                        · linarith only [h0, h528, h535, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
                      · linarith only [h384, h529, h532, h550, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h552 | h552
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h554 | h554
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h556 | h556
                                · linarith only [h530, h532, h556, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h559 | h559
                                    · linarith only [h528, h556, h559, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h561 | h561
                                      · linarith only [h310, h556, h561, hc01, hc34, hlam, hphi, ht12, ht23]
                                      · rcases h0bigk with h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c | h563c
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h0, hlam, p563_1]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h308, hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h310, hlam, p563_1]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h312, hlam, p563_1]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h0, h550, hc01, hc23, hlam, hphi, ht12, p563_1]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h384, hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h0, h528, h550, h558, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p563_1, u3ehi3]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h0, h528, h532, h550, h558, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p563_1, u3ehi3]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h308, hc01, hlam, hphi, p563_1, u1elo2]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h308, h529, hc25, hlam, hphi, ht01, ht0b, ht5b, p563_1, u1elo2]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h308, h528, h558, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p563_1, u1elo2, u3ehi3]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h308, h528, h532, h558, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p563_1, u1elo2, u3ehi3]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h310, hc01, hlam, hphi, p563_1, u1elo3]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h528, hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h530, hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h532, hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h312, hc01, hlam, hphi, p563_1, u1elo4]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h529, hlam, p563_1]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h531, hlam, p563_0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [h0, h529, h550, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p563_1, u4ehi0]
                                        · have p563_0 := h563c.1
                                          have p563_1 := h563c.2.1
                                          have p563_2 := h563c.2.2.1
                                          have p563_3 := h563c.2.2.2
                                          linarith only [hlam, p563_0]
                                  · linarith only [h0, h530, h550, h558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h308, h531, h555, hlam]
                            · linarith only [h308, h530, h554, hlam]
                          · linarith only [h0, h529, h553, hlam]
                        · linarith only [h0, h528, h552, hlam]
                  · linarith only [h530, h531, hc35, hlam, hphi, u3ehi3]
                · linarith only [h384, h528, h530, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
                · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
                    · linarith only [h528, h529, h598, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h600 | h600
                      · linarith only [h384, h528, h600, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                          · linarith only [h528, h529, h603, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h606 | h606
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h607 | h607
                                · linarith only [h596, h598, h602, h603, h606, h607, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h609 | h609
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
                                    · linarith only [h528, h607, h610, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                                    · linarith only [h0, h528, h603, h610, hc45, hlam, hphi, u4ehi2]
                                  · linarith only [h384, h528, h596, h609, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                              · linarith only [h308, h597, h606, hlam]
                            · linarith only [h308, h596, h605, hlam]
                        · linarith only [h0, h308, h528, h529, h597, h602, hc01, hlam, hphi, u1elo2]
                  · linarith only [h596, h597, hc35, hlam, hphi, u3ehi3]
                · linarith only [h384, h528, h596, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h619 | h619
              · rcases m.htr 0 3 4 (by decide) (by decide) with h620 | h620
                · rcases m.htr 0 3 5 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h622 | h622
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                      · linarith only [h384, h619, h623, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h625 | h625
                        · linarith only [h528, h619, h621, h625, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h629 | h629
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h631 | h631
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h632 | h632
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h633 | h633
                                      · linarith only [h620, h633, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                      · linarith only [h619, h632, h633, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                    · linarith only [h0, h622, h625, h632, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                                  · linarith only [h620, h631, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                                · linarith only [h310, h622, h630, hlam]
                              · linarith only [h308, h620, h629, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h308, h620, h628, hlam]
                          · linarith only [h0, h619, h627, hlam]
                    · linarith only [h528, h619, h622, hlam]
                  · linarith only [h620, h621, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
                  · linarith only [h620, h644, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h384, h619, h644, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h647 | h647
                · rcases m.htr 0 3 5 (by decide) (by decide) with h648 | h648
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
                      · linarith only [h0, h384, h650, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h652 | h652
                        · linarith only [h0, h528, h650, h652, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h654 | h654
                          · linarith only [h0, h619, h650, h654, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h656 | h656
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h657 | h657
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h658 | h658
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h660 | h660
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h661 | h661
                                      · linarith only [h647, h661, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                      · linarith only [h649, h661, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                    · linarith only [h0, h312, h528, h649, h656, h658, h660, hc01, hlam, hphi, u1elo2]
                                  · linarith only [h384, h647, h659, hlam]
                                · linarith only [h310, h649, h658, hlam]
                              · linarith only [h308, h647, h657, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h308, h647, h656, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h669 | h669
                      · linarith only [h0, h384, h669, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h671 | h671
                        · linarith only [h0, h528, h669, h671, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
                          · linarith only [h0, h619, h669, h673, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h675 | h675
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h676 | h676
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h677 | h677
                                · linarith only [h649, h675, h677, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                                    · linarith only [h0, h671, h677, h680, hc01, hc24, hlam, hphi, ht12]
                                    · linarith only [h0, h671, h680, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h647, h679, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h308, h647, h676, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h308, h647, h675, hlam]
                  · linarith only [h647, h648, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h687 | h687
                  · linarith only [h647, h687, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h689 | h689
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
                      · linarith only [h0, h384, h690, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h692 | h692
                        · linarith only [h0, h528, h692, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h694 | h694
                          · linarith only [h0, h619, h690, h694, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h696 | h696
                            · linarith only [h647, h696, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h698 | h698
                              · linarith only [h687, h696, h698, hc34, hlam, hphi, u3ehi0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h700 | h700
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h701 | h701
                                  · linarith only [h0, h690, h696, h701, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h690, h701, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h689, h700, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h705 | h705
                      · linarith only [h0, h384, h705, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h707 | h707
                        · linarith only [h0, h528, h705, h707, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h709 | h709
                          · linarith only [h0, h619, h705, h709, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h711 | h711
                            · linarith only [h647, h711, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h713 | h713
                              · linarith only [h711, h713, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h715 | h715
                                · linarith only [h647, h689, h715, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h717 | h717
                                  · linarith only [h0, h705, h711, h717, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h705, h717, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
