import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h11, h2, h7, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h11, h13, h4, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h11, h15, h4, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h10, h15, h8, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h1, h18, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h18, h20, h4, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h2, h22, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                          · linarith only [h0, h18, h20, h22, h24, h4, h6, h7, h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h24, h4, h5, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h27, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h29, h4, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h31, h4, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                      · linarith only [h0, h31, h33, h4, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h2, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                          · linarith only [h0, h31, h37, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h0, h37, h4, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                · linarith only [h0, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                    · linarith only [h1, h44, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h44, h5, h6, hc13, hc35, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                    · linarith only [h1, h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h47, h5, h6, hc13, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h50, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                  · linarith only [h0, h4, h40, h52, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h4, h40, h54, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h5, h54, h6, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
              · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                · linarith only [h0, h59, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                    · linarith only [h1, h5, h62, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h2, h65, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h59, h61, h65, hlam]
                      · linarith only [h5, h57, h64, hc13, hc34, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                    · linarith only [h1, h5, h69, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h58, h61, h71, hlam]
                      · linarith only [h5, h57, h71, hc13, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                · linarith only [h0, h74, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                  · linarith only [h0, h4, h58, h76, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                    · linarith only [h0, h4, h5, h58, h78, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                        · linarith only [h2, h81, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h78, h80, h81, hlam]
                      · linarith only [h5, h57, h80, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
              · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                · linarith only [h0, h86, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                    · linarith only [h1, h5, h89, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h1, h57, h91, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                        · linarith only [h2, h93, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h86, h88, h93, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                    · linarith only [h1, h5, h96, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h57, h85, h98, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                        · linarith only [h100, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                          · linarith only [h1, h102, h85, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h104 | h104
                            · linarith only [h100, h104, h3, h57, h85, h86, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                              · linarith only [h100, h102, h106, h85, h86, hc23, hc34, hlam, hphi]
                              · linarith only [h106, h85, h86, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                · linarith only [h0, h109, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                  · linarith only [h0, h111, h4, h85, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                    · linarith only [h0, h113, h4, h85, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h115, h4, h57, h85, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                        · linarith only [h117, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                          · linarith only [h0, h119, h2, h4, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h121, h4, h57, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                                · rcases h1bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    rcases p125_3 (m.d 0 1) (by simp) with h127 | h127
                                    · rcases p125_3 (m.d 1 2) (by simp) with h128 | h128
                                      · linarith only [h128, hlam, p125_0]
                                      · rcases p125_3 (m.d 1 3) (by simp) with h130 | h130
                                        · linarith only [h1, h130, hlam]
                                        · linarith only [h130, h85, hlam]
                                    · linarith only [h127, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    rcases p125_3 (m.d 0 1) (by simp) with h134 | h134
                                    · rcases p125_3 (m.d 1 2) (by simp) with h135 | h135
                                      · linarith only [h0, h135, hlam]
                                      · rcases p125_3 (m.d 1 3) (by simp) with h137 | h137
                                        · linarith only [h137, hlam, p125_0]
                                        · rcases p125_3 (m.d 1 4) (by simp) with h139 | h139
                                          · linarith only [h139, h2, hlam]
                                          · linarith only [h113, h139, hlam]
                                    · linarith only [h134, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo0, u4ehi1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h117, hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo0, u4ehi1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h0, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h85, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h109, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h111, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h1, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h1, h117, h119, h123, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p125_1, u0elo0, u4ehi1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h113, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h115, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h2, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h117, h119, h123, hc12, hc34, hlam, hphi, ht23, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h117, h119, h123, hc13, hc34, hlam, hphi, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h117, hlam, p125_1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h3, hlam, p125_0]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h117, h119, h123, h3, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p125_1, u0elo0, u4ehi1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h117, h119, h123, h3, h85, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p125_1, u0elo0, u4ehi1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [h3, hlam, hphi, ht0b, ht45, ht5b, p125_1, u0elo0, u4ehi1]
                                  · have p125_0 := h125c.1
                                    have p125_1 := h125c.2.1
                                    have p125_2 := h125c.2.2.1
                                    have p125_3 := h125c.2.2.2
                                    linarith only [hlam, p125_0]
                                · linarith only [h119, h123, h124, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                                · linarith only [h109, h123, h166, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h166, h4, h5, h85, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
          · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
            · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
              · linarith only [h0, h171, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                · linarith only [h0, h173, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h1, h176, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h169, h171, h175, h176, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                    · linarith only [h1, h179, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                      · linarith only [h1, h169, h179, h181, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h183, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                                · linarith only [h1, h169, h183, h188, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                                · linarith only [h171, h179, h185, h187, h188, hc12, hc23, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                                · linarith only [h1, h169, h187, h191, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                                · rcases h1bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    rcases p193_3 (m.d 0 1) (by simp) with h195 | h195
                                    · rcases p193_3 (m.d 1 2) (by simp) with h196 | h196
                                      · linarith only [h196, hlam, p193_0]
                                      · rcases p193_3 (m.d 1 3) (by simp) with h198 | h198
                                        · linarith only [h1, h198, hlam]
                                        · linarith only [h171, h198, hlam]
                                    · linarith only [h195, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    rcases p193_3 (m.d 0 1) (by simp) with h202 | h202
                                    · rcases p193_3 (m.d 1 2) (by simp) with h203 | h203
                                      · linarith only [h0, h203, hlam]
                                      · rcases p193_3 (m.d 1 3) (by simp) with h205 | h205
                                        · linarith only [h205, hlam, p193_0]
                                        · rcases p193_3 (m.d 1 4) (by simp) with h207 | h207
                                          · linarith only [h2, h207, hlam]
                                          · linarith only [h179, h207, hlam]
                                    · linarith only [h202, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht45, ht5b, p193_1, u0elo0, u4ehi1]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h183, hlam, hphi, ht0b, ht45, ht5b, p193_1, u0elo0, u4ehi1]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h0, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h171, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h173, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h175, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h1, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h1, h170, h179, h191, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h179, hlam, p193_1]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h181, hlam, p193_1]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h2, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h1, h170, h179, h191, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1, u0elo0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h183, hlam, p193_1]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h3, hlam, p193_0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h1, h170, h171, h181, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u0elo0]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [h1, h170, h181, hlam, hphi, ht0b, ht45, ht5b, p193_1, u0elo0, u4ehi1]
                                  · have p193_0 := h193c.1
                                    have p193_1 := h193c.2.1
                                    have p193_2 := h193c.2.2.1
                                    have p193_3 := h193c.2.2.2
                                    linarith only [hlam, p193_0]
                            · linarith only [h0, h1, h170, h186, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h169, h185, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
              · linarith only [h0, h169, h235, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                · linarith only [h0, h237, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                    · linarith only [h1, h240, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h169, h170, h240, hc13, hc35, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                    · linarith only [h1, h243, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h169, h170, h243, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
            · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
              · linarith only [h0, h247, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                · linarith only [h0, h249, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                    · linarith only [h1, h169, h252, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h2, h255, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h247, h251, h252, h255, hlam]
                      · linarith only [h169, h246, h247, h251, h254, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                    · linarith only [h1, h259, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h2, h262, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h259, h261, h262, hlam]
                      · linarith only [h169, h246, h261, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
              · linarith only [h0, h266, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h268 | h268
                · linarith only [h0, h268, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                    · linarith only [h1, h271, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                      · linarith only [h2, h246, h271, h273, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h266, h270, h273, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h276 | h276
                    · linarith only [h0, h1, h169, h276, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h278 | h278
                      · linarith only [h1, h246, h278, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                        · linarith only [h2, h280, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h284 | h284
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h285 | h285
                                · linarith only [h280, h282, h285, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                                · linarith only [h0, h169, h284, h285, h4, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                                · linarith only [h268, h284, h288, hc12, hc34, hlam, hphi, ht23]
                                · rcases h1bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    rcases p290_3 (m.d 0 1) (by simp) with h292 | h292
                                    · rcases p290_3 (m.d 1 2) (by simp) with h293 | h293
                                      · linarith only [h293, hlam, p290_0]
                                      · rcases p290_3 (m.d 1 3) (by simp) with h295 | h295
                                        · linarith only [h1, h295, hlam]
                                        · linarith only [h266, h295, hlam]
                                    · linarith only [h292, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    rcases p290_3 (m.d 0 1) (by simp) with h299 | h299
                                    · rcases p290_3 (m.d 1 2) (by simp) with h300 | h300
                                      · linarith only [h0, h300, hlam]
                                      · rcases p290_3 (m.d 1 3) (by simp) with h302 | h302
                                        · linarith only [h302, hlam, p290_0]
                                        · rcases p290_3 (m.d 1 4) (by simp) with h304 | h304
                                          · linarith only [h2, h304, hlam]
                                          · linarith only [h276, h304, hlam]
                                    · linarith only [h299, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht45, ht5b, p290_1, u0elo0, u4ehi1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h280, hlam, hphi, ht0b, ht45, ht5b, p290_1, u0elo0, u4ehi1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h0, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h266, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h268, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h270, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h1, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1, u0elo0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h276, hlam, p290_1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h278, hlam, p290_1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h2, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1, u0elo0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h169, h2, h282, h284, hc13, hc45, hlam, hphi, ht34, p290_1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h280, hlam, p290_1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h3, hlam, p290_0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1, u0elo0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h266, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p290_1, u0elo0]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [h3, hlam, hphi, ht0b, ht45, ht5b, p290_1, u0elo0, u4ehi1]
                                  · have p290_0 := h290c.1
                                    have p290_1 := h290c.2.1
                                    have p290_2 := h290c.2.2.1
                                    have p290_3 := h290c.2.2.2
                                    linarith only [hlam, p290_0]
                            · linarith only [h0, h169, h282, h283, h4, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                            · linarith only [h0, h246, h282, h331, h4, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                                · rcases h1bigk with h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    rcases p335_3 (m.d 0 1) (by simp) with h337 | h337
                                    · rcases p335_3 (m.d 1 2) (by simp) with h338 | h338
                                      · linarith only [h338, hlam, p335_0]
                                      · rcases p335_3 (m.d 1 3) (by simp) with h340 | h340
                                        · linarith only [h1, h340, hlam]
                                        · linarith only [h266, h340, hlam]
                                    · linarith only [h337, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    rcases p335_3 (m.d 0 1) (by simp) with h344 | h344
                                    · rcases p335_3 (m.d 1 2) (by simp) with h345 | h345
                                      · linarith only [h0, h345, hlam]
                                      · rcases p335_3 (m.d 1 3) (by simp) with h347 | h347
                                        · linarith only [h347, hlam, p335_0]
                                        · rcases p335_3 (m.d 1 4) (by simp) with h349 | h349
                                          · linarith only [h2, h349, hlam]
                                          · linarith only [h276, h349, hlam]
                                    · linarith only [h344, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht45, ht5b, p335_1, u0elo0, u4ehi1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h280, hlam, hphi, ht0b, ht45, ht5b, p335_1, u0elo0, u4ehi1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h0, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h266, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h268, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h270, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h1, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h1, h280, h282, h333, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p335_1, u0elo0, u4ehi1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h276, hlam, p335_1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h278, hlam, p335_1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h2, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h280, h282, h333, hc12, hc34, hlam, hphi, ht23, p335_1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h280, h282, h333, hc13, hc34, hlam, hphi, p335_1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h280, hlam, p335_1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h3, hlam, p335_0]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h280, h282, h3, h333, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p335_1, u0elo0, u4ehi1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h266, h280, h282, h3, h333, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p335_1, u0elo0, u4ehi1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [h3, hlam, hphi, ht0b, ht45, ht5b, p335_1, u0elo0, u4ehi1]
                                  · have p335_0 := h335c.1
                                    have p335_1 := h335c.2.1
                                    have p335_2 := h335c.2.2.1
                                    have p335_3 := h335c.2.2.2
                                    linarith only [hlam, p335_0]
                                · linarith only [h282, h333, h334, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h376 | h376
                                · linarith only [h0, h282, h333, h376, h4, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h282, h376, h4, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h379 | h379
        · rcases m.htr 0 3 4 (by decide) (by decide) with h380 | h380
          · rcases m.htr 0 3 5 (by decide) (by decide) with h381 | h381
            · linarith only [h0, h3, h379, h381, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
              · rcases m.htr 1 2 4 (by decide) (by decide) with h384 | h384
                · linarith only [h0, h384, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h2, h3, h384, h386, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                    · linarith only [h1, h3, h386, h388, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h380, h381, h388, hc13, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                · linarith only [h0, h3, h379, h383, h391, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                  · linarith only [h0, h3, h379, h383, h393, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h3, h379, h383, h393, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
            · linarith only [h1, h3, h396, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
              · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                · linarith only [h0, h399, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h401 | h401
                  · linarith only [h2, h3, h399, h401, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
                    · linarith only [h1, h3, h401, h403, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h405 | h405
                      · linarith only [h2, h3, h396, h398, h399, h401, h405, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h2, h3, h398, h399, h405, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                · linarith only [h0, h3, h379, h398, h408, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h410 | h410
                  · linarith only [h0, h3, h379, h398, h410, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                  · linarith only [h0, h3, h379, h398, h410, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h413 | h413
          · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
            · linarith only [h1, h3, h414, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
              · linarith only [h0, h3, h379, h416, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                · linarith only [h0, h3, h418, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                  · linarith only [h1, h3, h416, h420, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h422 | h422
                    · linarith only [h1, h3, h420, h422, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h413, h414, h416, h422, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
            · linarith only [h1, h3, h425, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
              · linarith only [h0, h379, h427, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                · linarith only [h1, h427, h429, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                  · linarith only [h1, h3, h427, h431, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                    · linarith only [h1, h3, h413, h431, h433, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                      · linarith only [h2, h3, h425, h433, h435, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h437 | h437
                        · linarith only [h2, h3, h435, h437, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h3, h437, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
      · rcases m.htr 0 2 3 (by decide) (by decide) with h441 | h441
        · rcases m.htr 0 3 4 (by decide) (by decide) with h442 | h442
          · linarith only [h0, h2, h441, h442, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h444 | h444
            · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
              · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                · linarith only [h0, h446, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h449 | h449
                    · linarith only [h0, h2, h442, h445, h446, h449, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h445, h449, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                    · linarith only [h0, h2, h445, h446, h452, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h2, h440, h445, h448, h452, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h455 | h455
                · linarith only [h0, h441, h445, h455, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · linarith only [h0, h2, h441, h445, h455, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                · linarith only [h0, h459, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                    · linarith only [h1, h2, h459, h462, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h2, h458, h462, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h465 | h465
                    · linarith only [h1, h2, h459, h465, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h2, h440, h458, h461, h465, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h468 | h468
                · linarith only [h0, h2, h441, h458, h468, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h2, h441, h458, h468, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h471 | h471
          · linarith only [h1, h2, h471, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
            · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
              · linarith only [h0, h2, h441, h474, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h476 | h476
                · linarith only [h0, h2, h476, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
                    · linarith only [h1, h2, h471, h476, h479, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h481 | h481
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                          · linarith only [h1, h2, h474, h479, h483, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h486 | h486
                              · linarith only [h1, h2, h474, h476, h478, h483, h486, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                              · linarith only [h1, h2, h474, h476, h478, h482, h486, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1, h2, h473, h476, h483, h485, hc23, hc34, hlam, hphi]
                        · linarith only [h1, h2, h474, h482, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1, h473, h474, h478, h481, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h492 | h492
                    · linarith only [h1, h2, h476, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h496 | h496
                          · linarith only [h1, h2, h492, h494, h496, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h498 | h498
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h499 | h499
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                                · linarith only [h1, h2, h476, h494, h496, h500, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                · linarith only [h1, h2, h476, h494, h495, h496, h500, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1, h2, h476, h494, h495, h499, hlam]
                            · linarith only [h1, h2, h476, h494, h496, h498, hc23, hc34, hlam, hphi]
                        · linarith only [h1, h2, h495, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h471, h473, h474, h494, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
              · linarith only [h0, h441, h507, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h509 | h509
                · linarith only [h0, h2, h509, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
                    · linarith only [h1, h2, h441, h471, h509, h512, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
                      · linarith only [h1, h473, h514, hlam]
                      · linarith only [h507, h511, h514, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h517 | h517
                    · linarith only [h1, h2, h517, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
                      · linarith only [h1, h473, h519, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                          · linarith only [h2, h440, h517, h521, h522, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                            · linarith only [h473, h522, h524, hc03, hc34, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h526 | h526
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h527 | h527
                                · rcases h1bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h2, h509, h522, hc12, hc34, hlam, hphi, ht23, p528_1]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h2, h509, h522, hc13, hc34, hlam, hphi, p528_1]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h2, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h2, h509, h521, h522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p528_1, u4ehi4]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h0, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h507, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h509, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h511, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h1, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h1, h2, h509, h522, hc12, hc34, hlam, hphi, ht23, p528_1]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h517, hlam, p528_1]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h519, hlam, p528_1]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h0, h509, h522, hc12, hc34, hlam, hphi, ht23, p528_1]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    rcases p528_3 (m.d 0 1) (by simp) with h545 | h545
                                    · linarith only [h2, h545, hlam]
                                    · linarith only [h0, h545, hlam]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    rcases p528_3 (m.d 0 1) (by simp) with h548 | h548
                                    · linarith only [h2, h548, hlam]
                                    · linarith only [h1, h548, hlam]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    rcases p528_3 (m.d 0 1) (by simp) with h552 | h552
                                    · linarith only [h2, h552, hlam]
                                    · linarith only [h440, h552, hlam]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h440, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h440, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p528_1, u0elo0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h440, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p528_1, u0elo0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [h521, hlam, p528_0]
                                  · have p528_0 := h528c.1
                                    have p528_1 := h528c.2.1
                                    have p528_2 := h528c.2.2.1
                                    have p528_3 := h528c.2.2.2
                                    linarith only [hlam, p528_0]
                                · linarith only [h2, h440, h509, h521, h522, h527, hlam]
                              · linarith only [h2, h440, h509, h521, h526, hlam]
                        · linarith only [h0, h2, h521, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h563 | h563
        · rcases m.htr 0 3 4 (by decide) (by decide) with h564 | h564
          · linarith only [h0, h2, h563, h564, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h566 | h566
            · linarith only [h0, h440, h563, h566, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
              · rcases m.htr 1 2 4 (by decide) (by decide) with h569 | h569
                · linarith only [h0, h569, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                  · linarith only [h0, h440, h571, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
                    · linarith only [h0, h2, h564, h568, h569, h573, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h568, h573, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
                · linarith only [h0, h2, h563, h568, h576, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                · linarith only [h0, h2, h563, h568, h576, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h579 | h579
          · linarith only [h1, h2, h579, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
            · linarith only [h1, h440, h581, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
              · linarith only [h0, h563, h583, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h585 | h585
                · linarith only [h0, h2, h585, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h587 | h587
                  · linarith only [h1, h440, h583, h587, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h589 | h589
                    · linarith only [h1, h2, h585, h589, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                      · linarith only [h1, h2, h581, h589, h591, hc03, hc34, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h594 | h594
                          · linarith only [h1, h440, h583, h589, h593, h594, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h596 | h596
                            · linarith only [h1, h440, h583, h591, h594, h596, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h598 | h598
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                                · rcases h1bigk with h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h440, h587, hc12, hc25, hlam, hphi, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h440, h587, h596, hc13, hc35, hlam, hphi, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h2, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h440, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h0, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h583, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h585, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h587, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h1, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h1, h440, h587, h596, hc12, hc35, hlam, hphi, ht23, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h589, hlam, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h591, hlam, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h1, h583, h585, h594, hc12, hc34, hlam, hphi, ht23, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    rcases p600_3 (m.d 0 1) (by simp) with h617 | h617
                                    · linarith only [h2, h617, hlam]
                                    · linarith only [h0, h617, hlam]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    rcases p600_3 (m.d 0 1) (by simp) with h620 | h620
                                    · linarith only [h2, h620, hlam]
                                    · linarith only [h1, h620, hlam]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h1, h440, h583, h585, h594, hc12, hc34, hlam, hphi, ht23, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h1, h583, h587, h594, h598, hc12, hc34, hlam, hphi, ht23, p600_1]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    rcases p600_3 (m.d 0 1) (by simp) with h626 | h626
                                    · linarith only [h440, h626, hlam]
                                    · linarith only [h0, h626, hlam]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    rcases p600_3 (m.d 0 1) (by simp) with h629 | h629
                                    · linarith only [h440, h629, hlam]
                                    · linarith only [h1, h629, hlam]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [h593, hlam, p600_0]
                                  · have p600_0 := h600c.1
                                    have p600_1 := h600c.2.1
                                    have p600_2 := h600c.2.2.1
                                    have p600_3 := h600c.2.2.2
                                    linarith only [hlam, p600_0]
                                · linarith only [h585, h593, h594, h599, hlam]
                              · linarith only [h585, h593, h598, hlam]
                        · linarith only [h1, h2, h583, h593, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h637 | h637
    · rcases m.htr 0 1 5 (by decide) (by decide) with h638 | h638
      · rcases m.htr 0 2 3 (by decide) (by decide) with h639 | h639
        · linarith only [h0, h1, h639, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h641 | h641
          · rcases m.htr 0 3 5 (by decide) (by decide) with h642 | h642
            · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
              · linarith only [h0, h639, h643, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h645 | h645
                · linarith only [h0, h1, h643, h645, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h647 | h647
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h649 | h649
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h650 | h650
                        · linarith only [h1, h637, h643, h650, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h645, h647, h650, hlam]
                      · linarith only [h0, h1, h647, h649, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h637, h648, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h656 | h656
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h657 | h657
                        · linarith only [h637, h657, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h660 | h660
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
                                · linarith only [h641, h657, h662, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
                                · rcases h1bigk with h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h1, h643, hc12, hc23, hlam, hphi, p664_1]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h1, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h1, h643, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p664_1, u4ehi3]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h1, h643, h655, h657, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p664_1, u4ehi3]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h0, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h643, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h645, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h647, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h0, h643, hc12, hc23, hlam, hphi, p664_1]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    rcases p664_3 (m.d 0 1) (by simp) with h676 | h676
                                    · linarith only [h1, h676, hlam]
                                    · linarith only [h0, h676, hlam]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    rcases p664_3 (m.d 0 1) (by simp) with h680 | h680
                                    · linarith only [h1, h680, hlam]
                                    · linarith only [h637, h680, hlam]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    rcases p664_3 (m.d 0 1) (by simp) with h683 | h683
                                    · linarith only [h1, h683, hlam]
                                    · linarith only [h638, h683, hlam]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h637, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h638, h657, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p664_1, u0elo0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h655, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h657, hlam, p664_1]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h638, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h1, h638, h643, hc12, hc23, hlam, hphi, p664_1]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h656, hlam, p664_0]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [h1, h638, h643, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p664_1, u4ehi1]
                                  · have p664_0 := h664c.1
                                    have p664_1 := h664c.2.1
                                    have p664_2 := h664c.2.2.1
                                    have p664_3 := h664c.2.2.2
                                    linarith only [hlam, p664_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h696 | h696
                                · linarith only [h637, h655, h661, h696, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                                · rcases h1bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h1, h643, hc12, hc23, hlam, hphi, p698_1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h1, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h1, h643, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p698_1, u4ehi1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h1, h643, h647, hc12, hc23, hlam, hphi, p698_1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h0, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h643, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h645, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h647, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h0, h643, hc12, hc23, hlam, hphi, p698_1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    rcases p698_3 (m.d 0 1) (by simp) with h710 | h710
                                    · linarith only [h1, h710, hlam]
                                    · linarith only [h0, h710, hlam]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    rcases p698_3 (m.d 0 1) (by simp) with h714 | h714
                                    · linarith only [h1, h714, hlam]
                                    · linarith only [h637, h714, hlam]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    rcases p698_3 (m.d 0 1) (by simp) with h717 | h717
                                    · linarith only [h1, h717, hlam]
                                    · linarith only [h638, h717, hlam]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h637, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h638, h657, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p698_1, u0elo0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h655, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h657, hlam, p698_1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h638, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h1, h638, h643, hc12, hc23, hlam, hphi, p698_1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h656, hlam, p698_0]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [h1, h638, h643, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p698_1, u4ehi1]
                                  · have p698_0 := h698c.1
                                    have p698_1 := h698c.2.1
                                    have p698_2 := h698c.2.2.1
                                    have p698_3 := h698c.2.2.2
                                    linarith only [hlam, p698_0]
                            · linarith only [h0, h1, h643, h660, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h638, h643, h655, h657, h659, hlam]
                      · linarith only [h0, h1, h656, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h637, h655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
            · linarith only [h1, h638, h642, hlam]
          · linarith only [h1, h637, h641, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h736 | h736
        · linarith only [h0, h1, h736, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h738 | h738
          · rcases m.htr 0 3 5 (by decide) (by decide) with h739 | h739
            · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
              · linarith only [h0, h736, h740, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                · linarith only [h0, h1, h740, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
                  · linarith only [h637, h638, h742, h744, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h746 | h746
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h748 | h748
                        · linarith only [h637, h638, h740, h747, h748, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h637, h638, h748, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h1, h637, h739, h746, h747, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                    · linarith only [h1, h637, h746, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
              · linarith only [h0, h1, h739, h753, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h755 | h755
                · linarith only [h0, h1, h739, h755, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h757 | h757
                  · linarith only [h637, h638, h755, h757, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h759 | h759
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h760 | h760
                      · linarith only [h1, h637, h739, h760, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h1, h637, h759, h760, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h1, h637, h759, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · linarith only [h1, h637, h738, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h765 | h765
      · rcases m.htr 0 2 3 (by decide) (by decide) with h766 | h766
        · linarith only [h0, h1, h766, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h768 | h768
          · rcases m.htr 0 3 5 (by decide) (by decide) with h769 | h769
            · rcases m.htr 1 2 3 (by decide) (by decide) with h770 | h770
              · linarith only [h0, h637, h766, h768, h770, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h772 | h772
                · linarith only [h0, h1, h770, h772, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h776 | h776
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h777 | h777
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h780 | h780
                              · linarith only [h0, h637, h770, h774, h775, h780, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h637, h772, h780, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h637, h770, h774, h775, h777, h779, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h637, h768, h770, h774, h775, h777, h778, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · linarith only [h0, h637, h777, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h637, h774, h775, h776, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h1, h768, h774, h775, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h790 | h790
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h791 | h791
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h792 | h792
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h793 | h793
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h794 | h794
                                · linarith only [h768, h794, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                · linarith only [h765, h790, h794, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                              · linarith only [h637, h765, h772, h790, h793, hlam]
                            · linarith only [h637, h765, h770, h788, h789, h792, hlam]
                          · linarith only [h637, h765, h770, h774, h788, h791, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h637, h765, h774, h790, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h637, h765, h774, h788, h789, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h768, h788, hlam]
            · linarith only [h1, h765, h769, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
            · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
              · linarith only [h0, h766, h804, h805, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h807 | h807
                · linarith only [h0, h1, h768, h807, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h810 | h810
                    · linarith only [h0, h1, h768, h805, h810, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h809, h810, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h813 | h813
                    · linarith only [h1, h765, h768, h805, h809, h813, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h765, h809, h813, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h765, h804, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h817 | h817
        · linarith only [h0, h1, h817, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h819 | h819
          · rcases m.htr 0 3 5 (by decide) (by decide) with h820 | h820
            · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
              · linarith only [h0, h765, h817, h821, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
                · linarith only [h0, h1, h821, h823, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h825 | h825
                  · linarith only [h0, h765, h825, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h827 | h827
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h828 | h828
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h829 | h829
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h831 | h831
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h832 | h832
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h833 | h833
                                · linarith only [h819, h833, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                · rcases h1bigk with h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h765, h821, h827, h829, hc12, hc23, hlam, hphi, p835_1]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h1, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h637, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h765, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h0, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h821, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h823, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h825, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h0, h821, hc12, hc23, hlam, hphi, p835_1]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    rcases p835_3 (m.d 0 1) (by simp) with h847 | h847
                                    · linarith only [h1, h847, hlam]
                                    · linarith only [h0, h847, hlam]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h821, h829, h833, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p835_1, u4ehi3]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h0, h765, h821, hc12, hc23, hlam, hphi, p835_1]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h0, h823, hc12, hc24, hlam, hphi, p835_1]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    rcases p835_3 (m.d 0 1) (by simp) with h854 | h854
                                    · linarith only [h637, h854, hlam]
                                    · linarith only [h0, h854, hlam]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h827, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h0, h765, h821, h827, hc12, hc23, hlam, hphi, p835_1]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h0, h825, hc12, hc25, hlam, hphi, p835_1]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    rcases p835_3 (m.d 0 1) (by simp) with h861 | h861
                                    · linarith only [h765, h861, hlam]
                                    · linarith only [h0, h861, hlam]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h828, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [h829, hlam, p835_0]
                                  · have p835_0 := h835c.1
                                    have p835_1 := h835c.2.1
                                    have p835_2 := h835c.2.2.1
                                    have p835_3 := h835c.2.2.2
                                    linarith only [hlam, p835_0]
                              · linarith only [h0, h637, h823, h832, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h820, h821, h831, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1, h819, h821, h830, hlam]
                        · linarith only [h0, h637, h829, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1, h820, h828, hlam]
                    · linarith only [h1, h819, h827, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h873 | h873
              · linarith only [h0, h1, h820, h873, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
                · linarith only [h0, h637, h819, h820, h875, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h877 | h877
                  · linarith only [h0, h765, h877, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h879 | h879
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
                      · linarith only [h0, h637, h819, h820, h873, h880, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h880, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h819, h879, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h884 | h884
            · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
              · linarith only [h0, h1, h819, h885, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
                · linarith only [h0, h765, h819, h884, h887, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h889 | h889
                  · linarith only [h0, h765, h889, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
                    · linarith only [h0, h765, h819, h884, h885, h891, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h891, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h894 | h894
              · linarith only [h0, h1, h884, h894, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                · linarith only [h0, h1, h884, h896, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h898 | h898
                  · linarith only [h0, h765, h898, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
                    · linarith only [h0, h1, h819, h894, h900, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h900, hc12, hc34, hlam, hphi, ht23]

end R2N4
