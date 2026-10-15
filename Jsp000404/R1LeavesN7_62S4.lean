import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3190000 in
set_option maxHeartbeats 3190000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h10, h12, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h0, h12, h14, h4, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h0, h14, h4, h7, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                      · linarith only [h0, h10, h11, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h10, h18, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                        · linarith only [h1, h20, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h2, h22, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h0, h22, h4, h7, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                        · linarith only [h1, h27, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h29, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                            · linarith only [h25, h27, h31, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                              · linarith only [h0, h25, h27, h33, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                                · linarith only [h31, h35, h7, h9, hlam]
                                · linarith only [h0, h26, h35, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                      · linarith only [h0, h25, h26, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h25, h39, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                        · linarith only [h1, h41, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                          · linarith only [h25, h41, h43, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                            · linarith only [h0, h25, h4, h41, h45, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h25, h45, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
                  · linarith only [h48, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                        · linarith only [h1, h52, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · linarith only [h52, h7, h8, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h50, h51, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h0, h4, h50, h56, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                        · linarith only [h1, h58, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · linarith only [h58, h7, h8, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                        · linarith only [h61, h65, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                          · linarith only [h2, h67, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h62, h67, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h6, h63, h64, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h4, h63, h71, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                        · linarith only [h1, h7, h73, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                          · linarith only [h2, h75, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h0, h5, h62, h75, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                  · linarith only [h61, h62, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                        · linarith only [h1, h7, h82, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h2, h84, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h79, h84, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h6, h80, h81, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                      · linarith only [h0, h4, h80, h88, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                        · linarith only [h4, h7, h80, h90, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                          · linarith only [h2, h92, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h0, h5, h79, h92, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
                        · linarith only [h1, h7, h97, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                          · linarith only [h2, h99, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                            · linarith only [h1, h101, h7, h95, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                              · linarith only [h1, h103, h61, h95, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                                · linarith only [h105, h5, h79, hlam]
                                · linarith only [h0, h105, h96, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                      · linarith only [h0, h6, h95, h96, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                      · linarith only [h0, h109, h4, h95, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                        · linarith only [h111, h4, h7, h95, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                          · linarith only [h113, h2, h79, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                            · linarith only [h115, h4, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                              · linarith only [h117, h4, h61, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                                · linarith only [h119, h4, h7, h79, h95, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                                  · linarith only [h121, h4, h7, h79, h95, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h121, h4, h7, h95, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
              · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
                · linarith only [h125, h4, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h127 | h127
                  · linarith only [h127, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h0, h130, h6, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                        · linarith only [h129, h130, h132, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · linarith only [h124, h125, h132, hc13, hc35, hlam, hphi]
                    · linarith only [h129, h4, h6, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h136 | h136
                · linarith only [h124, h136, h5, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h138, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                      · linarith only [h0, h141, h6, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                        · linarith only [h1, h124, h143, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                          · linarith only [h138, h145, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                            · linarith only [h1, h124, h140, h147, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                              · linarith only [h1, h136, h140, h149, h5, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                                · linarith only [h138, h151, h5, h6, hlam]
                                · linarith only [h151, h5, h6, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h140, h4, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h155 | h155
            · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
              · linarith only [h156, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h158 | h158
                · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                        · linarith only [h0, h156, h160, h162, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                          · linarith only [h164, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h159, h164, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h155, h161, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h160, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h158, h159, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                        · linarith only [h1, h156, h173, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                          · linarith only [h175, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h170, h175, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h155, h171, h172, h2, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h171, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h155, h170, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
              · linarith only [h181, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
                · linarith only [h155, h183, h4, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h187 | h187
                      · linarith only [h0, h155, h187, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h189 | h189
                        · linarith only [h0, h181, h186, h189, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                          · linarith only [h191, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h185, h191, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h186, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                      · linarith only [h0, h155, h196, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                        · linarith only [h0, h181, h195, h198, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                          · linarith only [h185, h200, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                            · linarith only [h0, h181, h195, h202, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                              · linarith only [h0, h183, h195, h204, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                                · linarith only [h0, h185, h195, h202, h206, h5, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h195, h206, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h195, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h210 | h210
          · rcases m.htr 0 2 5 (by decide) (by decide) with h211 | h211
            · rcases m.htr 0 3 4 (by decide) (by decide) with h212 | h212
              · rcases m.htr 0 3 5 (by decide) (by decide) with h213 | h213
                · rcases m.htr 0 4 5 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
                    · linarith only [h210, h215, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h218 | h218
                        · linarith only [h1, h218, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · linarith only [h212, h215, h217, h218, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h211, h217, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                    · linarith only [h211, h222, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                        · linarith only [h1, h225, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · linarith only [h212, h222, h224, h225, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h211, h224, h4, hc12, hc23, hlam, hphi]
                · linarith only [h211, h213, h4, hlam]
              · linarith only [h210, h212, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h231 | h231
              · rcases m.htr 0 3 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 0 4 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h210, h211, h233, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                    · linarith only [h0, h235, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h210, h211, h237, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                        · linarith only [h1, h239, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h233, h241, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                            · linarith only [h210, h235, h239, h243, h4, hc12, hc23, hlam, hphi]
                            · linarith only [h210, h231, h243, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h210, h232, h246, h4, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                    · linarith only [h210, h248, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
                      · linarith only [h210, h211, h250, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                        · linarith only [h1, h252, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · linarith only [h231, h232, h248, h252, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h210, h231, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h256 | h256
            · rcases m.htr 0 3 4 (by decide) (by decide) with h257 | h257
              · rcases m.htr 0 3 5 (by decide) (by decide) with h258 | h258
                · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                    · linarith only [h256, h260, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                        · linarith only [h1, h263, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · linarith only [h1, h257, h260, h262, h263, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h210, h256, h262, hc12, hc24, hlam, hphi]
                  · linarith only [h210, h256, h259, hlam]
                · linarith only [h210, h256, h257, h258, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                · rcases m.htr 0 4 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
                    · linarith only [h256, h271, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h273 | h273
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                        · linarith only [h1, h257, h274, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
                          · linarith only [h2, h276, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h270, h276, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h256, h273, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h256, h257, h270, h4, hlam]
                · linarith only [h256, h269, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h282 | h282
              · rcases m.htr 0 3 5 (by decide) (by decide) with h283 | h283
                · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                    · linarith only [h0, h285, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                      · linarith only [h0, h256, h287, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
                        · linarith only [h1, h289, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h291 | h291
                          · linarith only [h2, h291, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h284, h291, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                    · linarith only [h0, h282, h294, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h256, h296, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                        · linarith only [h1, h298, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h300 | h300
                          · linarith only [h284, h300, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
                                · linarith only [h282, h284, h294, h298, h302, h304, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                                  · linarith only [h210, h282, h304, h306, hlam]
                                  · rcases h0bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      rcases p308_3 (m.d 0 1) (by simp) with h310 | h310
                                      · rcases p308_3 (m.d 0 2) (by simp) with h311 | h311
                                        · linarith only [h0, h311, hlam]
                                        · rcases p308_3 (m.d 0 3) (by simp) with h313 | h313
                                          · linarith only [h1, h313, hlam]
                                          · linarith only [h313, h4, hlam]
                                      · linarith only [h0, h310, hlam]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h283, hc35, hlam, hphi, ht01, ht0b, ht5b, p308_1, u1elo0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h282, h294, h298, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p308_1, u1elo0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h3, h300, hlam, hphi, ht01, ht0b, ht45, ht5b, p308_1, u1elo0, u4ehi1]
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
                                      linarith only [h4, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h210, hlam, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h256, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h1, hlam, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      rcases p308_3 (m.d 0 1) (by simp) with h326 | h326
                                      · rcases p308_3 (m.d 0 2) (by simp) with h327 | h327
                                        · linarith only [h327, h4, hlam]
                                        · rcases p308_3 (m.d 0 3) (by simp) with h329 | h329
                                          · rcases p308_3 (m.d 0 4) (by simp) with h330 | h330
                                            · linarith only [h282, h330, hlam]
                                            · linarith only [h210, h330, hlam]
                                          · linarith only [h329, h4, hlam]
                                      · linarith only [h0, h326, hlam]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h282, h294, h298, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p308_1, u0elo2]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h1, h282, h284, h294, h298, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p308_1, u1elo0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h2, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h0, h210, h304, hc12, hc45, hlam, hphi, ht23, ht34, p308_1]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h282, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h284, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h3, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      rcases p308_3 (m.d 0 1) (by simp) with h344 | h344
                                      · rcases p308_3 (m.d 0 2) (by simp) with h345 | h345
                                        · linarith only [h256, h345, hlam]
                                        · rcases p308_3 (m.d 0 3) (by simp) with h347 | h347
                                          · rcases p308_3 (m.d 0 4) (by simp) with h348 | h348
                                            · linarith only [h284, h348, hlam]
                                            · linarith only [h210, h348, hlam]
                                          · linarith only [h347, h4, hlam]
                                      · linarith only [h0, h344, hlam]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [h283, hlam, p308_0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht45, ht5b, p308_1, u0elo4, u4ehi0]
                                    · have p308_0 := h308c.1
                                      have p308_1 := h308c.2.1
                                      have p308_2 := h308c.2.2.1
                                      have p308_3 := h308c.2.2.2
                                      linarith only [hlam, p308_0]
                              · linarith only [h282, h294, h298, h303, h4, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h282, h302, h4, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                  · linarith only [h282, h283, h358, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                    · linarith only [h0, h282, h360, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                      · linarith only [h1, h256, h360, h362, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                        · linarith only [h1, h364, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · linarith only [h282, h283, h364, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
                · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h369 | h369
                    · linarith only [h0, h369, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                      · linarith only [h0, h256, h371, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                        · linarith only [h1, h373, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                          · linarith only [h2, h375, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h368, h375, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · linarith only [h282, h367, h368, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h379 | h379
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h380 | h380
                    · linarith only [h0, h380, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                      · linarith only [h0, h256, h382, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h384 | h384
                        · linarith only [h1, h282, h384, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
                          · linarith only [h2, h386, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h379, h386, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                    · linarith only [h0, h389, h4, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                      · linarith only [h0, h256, h391, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                        · linarith only [h1, h393, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                          · linarith only [h2, h379, h395, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h400 | h400
                                  · linarith only [h2, h379, h397, h400, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                                  · linarith only [h0, h282, h399, h4, h400, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h403 | h403
                                  · linarith only [h2, h379, h397, h403, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                                  · rcases h0bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      rcases p405_3 (m.d 0 1) (by simp) with h407 | h407
                                      · rcases p405_3 (m.d 0 2) (by simp) with h408 | h408
                                        · linarith only [h0, h408, hlam]
                                        · rcases p405_3 (m.d 0 3) (by simp) with h410 | h410
                                          · linarith only [h1, h410, hlam]
                                          · linarith only [h4, h410, hlam]
                                      · linarith only [h0, h407, hlam]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      rcases p405_3 (m.d 0 1) (by simp) with h414 | h414
                                      · rcases p405_3 (m.d 0 2) (by simp) with h415 | h415
                                        · linarith only [h0, h415, hlam]
                                        · rcases p405_3 (m.d 0 3) (by simp) with h417 | h417
                                          · linarith only [h1, h417, hlam]
                                          · rcases p405_3 (m.d 0 4) (by simp) with h419 | h419
                                            · linarith only [h2, h419, hlam]
                                            · linarith only [h282, h419, hlam]
                                      · linarith only [h1, h414, hlam]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h2, hlam, hphi, ht01, ht0b, ht45, ht5b, p405_1, u1elo0, u4ehi1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h2, h379, hlam, hphi, ht01, ht0b, ht45, ht5b, p405_1, u1elo0, u4ehi1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h0, hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h4, hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h210, hlam, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h256, hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h1, hlam, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h0, h282, h397, h399, hc12, hc45, hlam, hphi, ht23, ht34, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h282, hlam, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h367, hlam, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h2, hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h0, h210, h399, hc12, hc45, hlam, hphi, ht23, ht34, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h282, h397, h399, hc03, hc45, hlam, hphi, ht34, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h379, hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h3, hlam, p405_0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h0, h367, h398, hc12, hc23, hlam, hphi, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [h0, h367, h398, h4, hc12, hc23, hlam, hphi, p405_1]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht45, ht5b, p405_1, u0elo4, u4ehi0]
                                    · have p405_0 := h405c.1
                                      have p405_1 := h405c.2.1
                                      have p405_2 := h405c.2.2.1
                                      have p405_3 := h405c.2.2.2
                                      linarith only [hlam, p405_0]
                              · linarith only [h0, h282, h397, h398, h4, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h446 | h446
                              · linarith only [h0, h367, h397, h4, h446, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
                                  · rcases h0bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      rcases p450_3 (m.d 0 1) (by simp) with h452 | h452
                                      · rcases p450_3 (m.d 0 2) (by simp) with h453 | h453
                                        · linarith only [h0, h453, hlam]
                                        · rcases p450_3 (m.d 0 3) (by simp) with h455 | h455
                                          · linarith only [h1, h455, hlam]
                                          · linarith only [h4, h455, hlam]
                                      · linarith only [h0, h452, hlam]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      rcases p450_3 (m.d 0 1) (by simp) with h459 | h459
                                      · rcases p450_3 (m.d 0 2) (by simp) with h460 | h460
                                        · linarith only [h0, h460, hlam]
                                        · rcases p450_3 (m.d 0 3) (by simp) with h462 | h462
                                          · linarith only [h1, h462, hlam]
                                          · rcases p450_3 (m.d 0 4) (by simp) with h464 | h464
                                            · linarith only [h2, h464, hlam]
                                            · linarith only [h282, h464, hlam]
                                      · linarith only [h1, h459, hlam]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h2, hlam, hphi, ht01, ht0b, ht45, ht5b, p450_1, u1elo0, u4ehi1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h3, h395, hlam, hphi, ht01, ht0b, ht45, ht5b, p450_1, u1elo0, u4ehi1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h0, hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h4, hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h210, hlam, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h256, hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h1, hlam, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h0, h4, h446, h449, hc12, hc34, hlam, hphi, ht23, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h282, hlam, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h367, hlam, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h2, hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h0, h379, h397, h448, hc12, hc34, hlam, hphi, ht23, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h379, h397, h448, hc03, hc34, hlam, hphi, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h379, hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h3, hlam, p450_0]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h0, h379, h397, h448, hc12, hc34, hlam, hphi, ht23, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h1, h379, h389, h397, h448, hc12, hc34, hlam, hphi, ht23, p450_1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [h2, h379, h397, h448, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p450_1, u4ehi1]
                                    · have p450_0 := h450c.1
                                      have p450_1 := h450c.2.1
                                      have p450_2 := h450c.2.2.1
                                      have p450_3 := h450c.2.2.2
                                      linarith only [hlam, p450_0]
                                  · linarith only [h397, h448, h449, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h491 | h491
                                  · linarith only [h0, h397, h4, h448, h491, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h397, h4, h491, hc12, hc45, hlam, hphi, ht23, ht34]
      · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h495 | h495
      · rcases m.htr 0 2 3 (by decide) (by decide) with h496 | h496
        · rcases m.htr 0 2 4 (by decide) (by decide) with h497 | h497
          · linarith only [h0, h2, h497, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h499 | h499
            · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
              · linarith only [h1, h2, h500, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
                · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                    · linarith only [h0, h2, h504, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h496, h504, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h496, h502, h503, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                    · linarith only [h0, h2, h509, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h496, h509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h2, h499, h508, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h513 | h513
              · linarith only [h1, h2, h513, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h515 | h515
                · linarith only [h496, h499, h515, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h517 | h517
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
                    · linarith only [h0, h2, h518, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h2, h495, h496, h499, h518, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h2, h495, h517, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h522 | h522
          · linarith only [h0, h2, h522, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h524 | h524
            · rcases m.htr 0 3 4 (by decide) (by decide) with h525 | h525
              · linarith only [h1, h2, h525, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h527 | h527
                · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                    · linarith only [h496, h524, h529, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h531 | h531
                      · linarith only [h0, h2, h531, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · linarith only [h496, h524, h531, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h495, h528, hlam]
                · linarith only [h496, h524, h527, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h536 | h536
              · linarith only [h1, h2, h536, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h538 | h538
                · rcases m.htr 0 4 5 (by decide) (by decide) with h539 | h539
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
                    · linarith only [h0, h2, h496, h540, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h542 | h542
                      · linarith only [h0, h2, h524, h542, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h544 | h544
                        · linarith only [h1, h2, h536, h544, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h546 | h546
                          · linarith only [h2, h495, h546, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
                          · linarith only [h2, h539, h546, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1, h2, h538, h539, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h550 | h550
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h551 | h551
                    · linarith only [h0, h2, h496, h551, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                      · linarith only [h1, h524, h538, h551, h553, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                        · linarith only [h1, h536, h550, h555, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
                          · linarith only [h2, h495, h557, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
                          · linarith only [h1, h2, h550, h551, h557, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h2, h495, h550, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h561 | h561
        · rcases m.htr 0 2 4 (by decide) (by decide) with h562 | h562
          · linarith only [h0, h2, h562, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h564 | h564
            · linarith only [h0, h495, h564, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h566 | h566
              · linarith only [h1, h2, h566, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h568 | h568
                · linarith only [h0, h495, h561, h568, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h570 | h570
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
                    · linarith only [h0, h2, h571, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h561, h571, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                    · linarith only [h0, h2, h574, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h561, h574, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h577 | h577
          · linarith only [h1, h2, h561, h577, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h579 | h579
            · linarith only [h1, h495, h561, h579, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h581 | h581
              · linarith only [h1, h2, h581, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
                · linarith only [h1, h495, h583, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h585 | h585
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
                    · linarith only [h0, h2, h561, h586, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h588 | h588
                      · linarith only [h0, h495, h579, h588, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                        · linarith only [h1, h581, h590, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h592 | h592
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
                            · linarith only [h1, h495, h586, h590, h592, h593, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h595 | h595
                              · linarith only [h1, h495, h583, h586, h593, h595, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h597 | h597
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h598 | h598
                                  · rcases h0bigk with h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c | h599c
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p599_1, u1elo3]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h1, h2, h586, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p599_1, u1elo3]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h2, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h495, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h0, hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h561, hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h577, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h579, hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h1, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h0, h1, h495, h592, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p599_1, u1elo3]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h581, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h583, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, p599_1, u1elo3]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      rcases p599_3 (m.d 0 1) (by simp) with h616 | h616
                                      · linarith only [h2, h616, hlam]
                                      · linarith only [h0, h616, hlam]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      rcases p599_3 (m.d 0 1) (by simp) with h619 | h619
                                      · linarith only [h2, h619, hlam]
                                      · linarith only [h1, h619, hlam]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [hlam, p599_0]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h1, h2, h495, h586, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p599_1, u1elo3]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h1, h586, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p599_1, u0elo4]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      rcases p599_3 (m.d 0 1) (by simp) with h625 | h625
                                      · linarith only [h495, h625, hlam]
                                      · linarith only [h0, h625, hlam]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      rcases p599_3 (m.d 0 1) (by simp) with h628 | h628
                                      · linarith only [h495, h628, hlam]
                                      · linarith only [h1, h628, hlam]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [h585, hlam, p599_1]
                                    · have p599_0 := h599c.1
                                      have p599_1 := h599c.2.1
                                      have p599_2 := h599c.2.2.1
                                      have p599_3 := h599c.2.2.2
                                      linarith only [hlam, p599_0]
                                  · linarith only [h581, h585, h598, hlam]
                                · linarith only [h585, h597, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h2, h585, h592, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
                    · linarith only [h0, h561, h636, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
                      · linarith only [h0, h2, h638, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                        · linarith only [h1, h2, h640, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                          · linarith only [h585, h642, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                          · linarith only [h1, h2, h636, h642, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h645 | h645
    · linarith only [h1, h645, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h647 | h647
      · rcases m.htr 0 2 3 (by decide) (by decide) with h648 | h648
        · linarith only [h0, h1, h648, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h650 | h650
          · linarith only [h0, h1, h650, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h652 | h652
            · rcases m.htr 0 3 4 (by decide) (by decide) with h653 | h653
              · rcases m.htr 0 3 5 (by decide) (by decide) with h654 | h654
                · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
                    · linarith only [h648, h652, h656, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h658 | h658
                      · linarith only [h0, h1, h658, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h650, h652, h658, hc12, hc24, hlam, hphi]
                  · linarith only [h645, h647, h655, hlam]
                · linarith only [h0, h1, h652, h654, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 4 5 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
                    · linarith only [h0, h645, h665, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                      · linarith only [h0, h645, h667, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · linarith only [h0, h645, h652, h667, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h645, h647, h664, hlam]
                · linarith only [h0, h1, h652, h663, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h672 | h672
              · rcases m.htr 0 3 5 (by decide) (by decide) with h673 | h673
                · rcases m.htr 0 4 5 (by decide) (by decide) with h674 | h674
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h675 | h675
                    · linarith only [h0, h645, h675, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h677 | h677
                      · linarith only [h0, h645, h652, h677, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
                          · linarith only [h645, h647, h679, h680, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                          · linarith only [h645, h672, h674, h680, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h647, h677, h679, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h645, h647, h674, hlam]
                · linarith only [h1, h647, h672, h673, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h686 | h686
                · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h688 | h688
                    · linarith only [h0, h1, h688, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h690 | h690
                      · linarith only [h0, h1, h652, h690, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h692 | h692
                        · linarith only [h1, h672, h692, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1, h647, h690, h692, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h645, h647, h687, hlam]
                · linarith only [h1, h647, h686, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h697 | h697
        · linarith only [h0, h1, h697, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h699 | h699
          · linarith only [h0, h1, h699, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h701 | h701
            · linarith only [h0, h647, h701, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h703 | h703
              · rcases m.htr 0 3 5 (by decide) (by decide) with h704 | h704
                · rcases m.htr 0 4 5 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h706 | h706
                    · linarith only [h0, h1, h706, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                      · linarith only [h0, h1, h701, h708, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h711 | h711
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h713 | h713
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h714 | h714
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h715 | h715
                                  · linarith only [h703, h715, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                  · linarith only [h705, h715, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                · linarith only [h699, h705, h714, hlam]
                              · linarith only [h645, h704, h705, h706, h710, h713, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi4]
                            · linarith only [h0, h647, h706, h710, h711, h712, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h705, h711, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h0, h1, h710, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
                    · linarith only [h0, h1, h723, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
                      · linarith only [h0, h1, h725, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                          · linarith only [h705, h727, h728, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                          · linarith only [h0, h645, h728, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h703, h727, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
                  · linarith only [h703, h704, h732, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                    · linarith only [h0, h697, h703, h734, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                      · linarith only [h0, h645, h736, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                          · linarith only [h0, h645, h732, h738, h739, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h645, h739, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h703, h704, h738, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h743 | h743
                · rcases m.htr 0 4 5 (by decide) (by decide) with h744 | h744
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
                    · linarith only [h0, h647, h697, h743, h745, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
                      · linarith only [h0, h647, h701, h747, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h749 | h749
                        · linarith only [h0, h647, h703, h743, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h749, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h703, h743, h744, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h753 | h753
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h754 | h754
                    · linarith only [h0, h1, h754, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h756 | h756
                      · linarith only [h0, h1, h756, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h758 | h758
                        · linarith only [h1, h703, h758, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h758, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
                    · linarith only [h0, h1, h761, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h763 | h763
                      · linarith only [h0, h1, h763, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h765 | h765
                        · linarith only [h1, h703, h765, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1, h765, hc12, hc34, hlam, hphi, ht23]

end R2N4
