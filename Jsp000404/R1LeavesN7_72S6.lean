import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h12, h6, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h11, h5, hc14, hlam, hphi, u4elo0]
                      · linarith only [h10, h4, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                          · linarith only [h17, h19, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                            · linarith only [h0, h19, h21, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h17, h21, h9, hc23, hlam, hphi, u3elo3]
                        · linarith only [h18, h5, h9, hc13, hlam, hphi, ht34, u4elo0]
                      · linarith only [h17, h4, h6, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                      · linarith only [h27, h6, h8, hlam]
                      · linarith only [h27, h4, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h26, h30, h6, h8, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h30, h4, hc13, hlam, hphi, u3elo0]
                · linarith only [h6, h7, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                              · linarith only [h34, h41, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h38, h39, h41, hc34, hlam, hphi, u4elo1]
                            · linarith only [h34, h39, h40, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h34, h39, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h38, h5, hc14, hlam, hphi, u4elo0]
                      · linarith only [h34, h37, h4, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h34, h36, h6, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                        · linarith only [h34, h35, h51, hlam]
                        · linarith only [h5, h51, hc14, hlam, hphi, u4elo0]
                      · linarith only [h4, h50, hc13, hlam, hphi, u3elo0]
                    · linarith only [h34, h49, h6, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                                · linarith only [h1, h57, h63, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h5, h63, hc34, hlam, hphi, u4elo0]
                              · linarith only [h34, h56, h59, h61, h62, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h34, h60, h61, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h6, h60, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h5, h59, hc14, hlam, hphi, u4elo0]
                      · linarith only [h4, h58, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                          · linarith only [h56, h57, h6, h73, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h56, h6, h73, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                        · linarith only [h5, h56, h57, h6, h72, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                      · linarith only [h4, h56, h6, h71, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                                · linarith only [h1, h78, h84, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h5, h84, hc34, hlam, hphi, u4elo0]
                              · linarith only [h80, h83, hc24, hlam, hphi, u4elo1]
                            · linarith only [h4, h6, h82, hc13, hlam, hphi, u3elo0]
                          · linarith only [h6, h81, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h5, h80, hc14, hlam, hphi, u4elo0]
                      · linarith only [h4, h79, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                          · linarith only [h78, h92, h94, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h6, h94, hc12, hlam, hphi, ht23, u3elo3]
                        · linarith only [h5, h78, h92, h93, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                      · linarith only [h4, h92, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
              · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h104, h5, hc04, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                          · linarith only [h0, h106, h99, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h102, h106, hc23, hlam, hphi, u3elo1]
                      · linarith only [h103, h4, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                        · linarith only [h111, h2, h5, hlam]
                        · linarith only [h102, h110, h111, hlam]
                      · linarith only [h110, h4, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                      · linarith only [h101, h116, h99, hlam]
                      · linarith only [h116, h4, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                      · linarith only [h100, h101, h115, h119, h2, h5, hc24, hlam, hphi, u4elo4]
                      · linarith only [h119, h4, hc13, hlam, hphi, u3elo0]
                · linarith only [h100, h99, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h127, h2, h5, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h123, h131, h5, h99, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                                · linarith only [h123, h129, h133, h2, h5, hlam]
                                · rcases h1bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h124, hc25, hlam, hphi, ht0b, ht5b, p135_1, u0elo0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h124, h130, h99, hc35, hlam, hphi, ht0b, ht5b, p135_1, u0elo0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    rcases p135_3 (m.d 0 1) (by simp) with h139 | h139
                                    · rcases p135_3 (m.d 1 2) (by simp) with h140 | h140
                                      · linarith only [h0, h140, hlam]
                                      · linarith only [h123, h140, hlam]
                                    · linarith only [h139, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    rcases p135_3 (m.d 0 1) (by simp) with h144 | h144
                                    · rcases p135_3 (m.d 1 2) (by simp) with h145 | h145
                                      · linarith only [h0, h145, hlam]
                                      · linarith only [h124, h145, hlam]
                                    · linarith only [h144, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h0, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h99, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h123, h129, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p135_1, u3elo2]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h99, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p135_1, u3elo2]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h1, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, p135_1, u3elo1]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h1, h123, h129, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1, u0elo0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h1, h124, h129, h131, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1, u0elo0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h2, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h123, hlam, p135_1]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h125, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h127, hlam, p135_1]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h3, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h124, hlam, p135_1]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h126, hlam, p135_0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [h123, h129, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1, u0elo0]
                                  · have p135_0 := h135c.1
                                    have p135_1 := h135c.2.1
                                    have p135_2 := h135c.2.2.1
                                    have p135_3 := h135c.2.2.2
                                    linarith only [hlam, p135_0]
                            · linarith only [h130, h99, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h123, h129, h99, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h126, h4, hc13, hlam, hphi, u3elo0]
                    · linarith only [h123, h125, h99, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h175, h2, h5, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                              · linarith only [h123, h124, h179, h3, h5, hlam]
                              · linarith only [h123, h124, h177, h179, hc34, hlam, hphi, u4elo4]
                            · linarith only [h174, h178, hc23, hlam, hphi, u3elo1]
                          · linarith only [h177, h99, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h174, h4, hc13, hlam, hphi, u3elo0]
                    · linarith only [h123, h173, h99, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                        · linarith only [h189, h2, h5, hlam]
                        · linarith only [h123, h186, h189, hlam]
                      · linarith only [h123, h186, h187, h188, h2, h4, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u4elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                        · linarith only [h194, h2, h5, hlam]
                        · linarith only [h186, h187, h194, h99, hlam]
                      · linarith only [h186, h193, h4, h99, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                        · linarith only [h2, h200, h5, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                              · linarith only [h204, h5, hc04, hlam, hphi, u4elo2]
                              · linarith only [h123, h204, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h123, h202, h203, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h202, h99, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h199, h4, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                        · linarith only [h2, h211, h5, hlam]
                        · linarith only [h198, h210, h211, hlam]
                      · linarith only [h210, h4, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
            · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
              · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                      · linarith only [h220, h4, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                        · linarith only [h219, h220, h222, hlam]
                        · linarith only [h215, h222, hc14, hlam, hphi, u4elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                      · linarith only [h1, h225, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                          · linarith only [h219, h228, hc13, hlam, hphi, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h1, h216, h230, h4, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                              · linarith only [h0, h217, h232, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h227, h232, hc24, hlam, hphi, u4elo1]
                        · linarith only [h215, h227, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h1, h237, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                        · linarith only [h217, h218, h239, hlam]
                        · linarith only [h215, h239, hc14, hlam, hphi, u4elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                      · linarith only [h236, h242, h4, hc03, hlam, hphi, ht34, u4elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                        · linarith only [h217, h218, h244, hlam]
                        · linarith only [h215, h244, hc14, hlam, hphi, u4elo0]
                · linarith only [h216, h217, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h251 | h251
                      · linarith only [h1, h251, h4, hlam]
                      · linarith only [h216, h249, h251, hlam]
                    · linarith only [h216, h248, h250, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h255 | h255
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h256 | h256
                      · linarith only [h1, h256, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                        · linarith only [h216, h248, h256, h258, hlam]
                        · linarith only [h215, h258, hc14, hlam, hphi, u4elo0]
                    · linarith only [h216, h248, h255, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h263 | h263
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                      · linarith only [h1, h264, h4, hlam]
                      · linarith only [h248, h262, h263, h264, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                      · linarith only [h1, h267, h4, hlam]
                      · linarith only [h216, h262, h267, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                      · linarith only [h1, h271, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                        · linarith only [h270, h271, h273, hlam]
                        · linarith only [h1, h215, h248, h270, h273, h4, hc12, hc34, hlam, hphi, ht23, u3elo4, u4elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                      · linarith only [h270, h276, h4, hc03, hlam, hphi, ht34, u4elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                          · linarith only [h270, h279, hc13, hlam, hphi, u3elo2]
                          · linarith only [h216, h279, hc12, hlam, hphi, ht23, ht34, u4elo3]
                        · linarith only [h215, h278, hc14, hlam, hphi, u4elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
              · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
                · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h287 | h287
                      · linarith only [h1, h287, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                        · linarith only [h215, h289, hc04, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                          · linarith only [h0, h283, h291, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h286, h291, h4, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h294 | h294
                      · linarith only [h2, h215, h286, h294, h4, hc03, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
                        · linarith only [h2, h215, h296, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                          · linarith only [h0, h283, h298, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h300 | h300
                            · linarith only [h300, h4, hc03, hlam, hphi, u3elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h302 | h302
                              · linarith only [h0, h215, h284, h302, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                                · linarith only [h2, h215, h283, h286, h304, hc23, hlam, hphi, ht34, u4elo3]
                                · linarith only [h283, h286, h304, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                      · linarith only [h1, h308, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                        · linarith only [h2, h215, h310, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h312 | h312
                          · linarith only [h0, h283, h312, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h307, h312, h4, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
                      · linarith only [h2, h215, h307, h315, h4, hc03, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h317 | h317
                        · linarith only [h2, h215, h317, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                          · linarith only [h307, h319, hc13, hlam, hphi, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                            · linarith only [h283, h285, h3, h307, h321, h4, hc12, hlam, hphi, ht23, u3elo3]
                            · linarith only [h284, h285, h319, h321, hc23, hlam, hphi, u3elo4]
                · linarith only [h283, h284, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
                · rcases m.htr 1 2 5 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h328 | h328
                      · linarith only [h1, h328, h4, hlam]
                      · linarith only [h283, h326, h328, hlam]
                    · linarith only [h283, h325, h327, hc24, hlam, hphi, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h333 | h333
                      · linarith only [h1, h333, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                        · linarith only [h2, h215, h335, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                            · linarith only [h1, h283, h325, h337, h338, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h283, h325, h337, h338, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h283, h325, h337, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h283, h325, h332, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                      · linarith only [h345, h4, hc03, hlam, hphi, u3elo1]
                      · linarith only [h2, h215, h325, h343, h344, h345, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                      · linarith only [h2, h215, h344, h348, h4, hc03, hlam, hphi, ht34, u4elo4]
                      · linarith only [h283, h343, h348, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                      · linarith only [h1, h352, h4, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                        · linarith only [h2, h215, h354, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                            · linarith only [h1, h351, h357, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h283, h357, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h1, h283, h351, h356, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                      · linarith only [h2, h215, h351, h361, h4, hc03, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                        · linarith only [h2, h215, h363, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                          · linarith only [h283, h351, h365, hc12, hlam, hphi, ht23, u3elo2]
                          · linarith only [h283, h365, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h368 | h368
          · linarith only [h1, h3, h368, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
            · linarith only [h2, h3, h370, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
              · linarith only [h0, h3, h368, h372, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
                · linarith only [h1, h3, h370, h372, h374, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h376 | h376
                  · linarith only [h1, h3, h372, h376, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
                    · linarith only [h1, h3, h370, h378, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h380 | h380
                      · linarith only [h2, h3, h368, h370, h378, h380, hc03, hlam, hphi, ht34, u4elo4]
                      · linarith only [h2, h3, h372, h378, h380, hc12, hlam, hphi, ht23, u3elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h385 | h385
    · rcases m.htr 0 1 4 (by decide) (by decide) with h386 | h386
      · rcases m.htr 0 1 5 (by decide) (by decide) with h387 | h387
        · rcases m.htr 0 3 5 (by decide) (by decide) with h388 | h388
          · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
            · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
              · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h399 | h399
                                · linarith only [h385, h390, h396, h399, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h389, h399, hc34, hlam, hphi, u4elo0]
                              · linarith only [h385, h393, h395, h398, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h388, h396, h397, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h0, h385, h393, h396, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h389, h395, hc14, hlam, hphi, u4elo0]
                      · linarith only [h388, h394, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h409 | h409
                          · linarith only [h393, h407, h409, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h411 | h411
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                                · rcases h1bigk with h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c | h414c
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h0, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h0, h390, h411, h413, hc45, hlam, hphi, ht0b, ht5b, p414_1, u0elo1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h0, h390, h393, h411, h413, hc45, hlam, hphi, ht0b, ht5b, p414_1, u0elo1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h419 | h419
                                    · rcases p414_3 (m.d 1 2) (by simp) with h420 | h420
                                      · rcases p414_3 (m.d 1 3) (by simp) with h421 | h421
                                        · linarith only [h385, h421, hlam]
                                        · linarith only [h407, h421, hlam]
                                      · linarith only [h392, h420, hlam]
                                    · linarith only [h419, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h385, h390, h411, h413, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h428 | h428
                                    · linarith only [h0, h428, hlam]
                                    · linarith only [h385, h428, hlam]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h431 | h431
                                    · linarith only [h0, h431, hlam]
                                    · linarith only [h386, h431, hlam]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    rcases p414_3 (m.d 0 1) (by simp) with h434 | h434
                                    · linarith only [h0, h434, hlam]
                                    · linarith only [h387, h434, hlam]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h385, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h390, hlam, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h393, hlam, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h393, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p414_1, u4elo3]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h386, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h391, hlam, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h0, h386, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h0, h386, h407, h413, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h387, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h392, hlam, p414_1]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h407, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [h408, hlam, p414_0]
                                  · have p414_0 := h414c.1
                                    have p414_1 := h414c.2.1
                                    have p414_2 := h414c.2.2.1
                                    have p414_3 := h414c.2.2.2
                                    linarith only [hlam, p414_0]
                                · linarith only [h390, h393, h411, h413, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                              · linarith only [h0, h387, h408, h409, h411, h412, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h388, h411, hc23, hlam, hphi, u3elo0]
                        · linarith only [h389, h408, hc14, hlam, hphi, u4elo0]
                      · linarith only [h388, h407, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h387, h392, hlam]
                · linarith only [h0, h385, h390, h391, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h390, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
              · rcases m.htr 1 2 4 (by decide) (by decide) with h461 | h461
                · rcases m.htr 1 2 5 (by decide) (by decide) with h462 | h462
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h464 | h464
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                        · linarith only [h386, h389, h465, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h467 | h467
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h469 | h469
                              · linarith only [h386, h389, h461, h469, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                                · linarith only [h385, h389, h460, h467, h471, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases h1bigk with h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h0, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h0, h460, h468, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    rcases p473_3 (m.d 0 1) (by simp) with h477 | h477
                                    · rcases p473_3 (m.d 1 2) (by simp) with h478 | h478
                                      · rcases p473_3 (m.d 1 3) (by simp) with h479 | h479
                                        · linarith only [h385, h479, hlam]
                                        · linarith only [h463, h479, hlam]
                                      · linarith only [h461, h478, hlam]
                                    · linarith only [h477, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    rcases p473_3 (m.d 0 1) (by simp) with h484 | h484
                                    · rcases p473_3 (m.d 1 2) (by simp) with h485 | h485
                                      · rcases p473_3 (m.d 1 3) (by simp) with h486 | h486
                                        · linarith only [h385, h486, hlam]
                                        · linarith only [h464, h486, hlam]
                                      · linarith only [h462, h485, hlam]
                                    · linarith only [h484, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h385, h460, h468, h471, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    rcases p473_3 (m.d 0 1) (by simp) with h493 | h493
                                    · linarith only [h0, h493, hlam]
                                    · linarith only [h385, h493, hlam]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    rcases p473_3 (m.d 0 1) (by simp) with h496 | h496
                                    · linarith only [h0, h496, hlam]
                                    · linarith only [h386, h496, hlam]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    rcases p473_3 (m.d 0 1) (by simp) with h499 | h499
                                    · linarith only [h0, h499, hlam]
                                    · linarith only [h387, h499, hlam]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h385, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h460, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h385, hc14, hlam, hphi, ht0b, ht45, ht5b, p473_1, u0elo0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h0, h385, h461, h465, h467, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h386, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h461, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h463, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h465, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h387, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h462, hlam, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h464, hlam, p473_0]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [h0, h387, h461, h467, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p473_1]
                                  · have p473_0 := h473c.1
                                    have p473_1 := h473c.2.1
                                    have p473_2 := h473c.2.2.1
                                    have p473_3 := h473c.2.2.2
                                    linarith only [hlam, p473_0]
                            · linarith only [h388, h468, hc23, hlam, hphi, u3elo0]
                          · linarith only [h0, h385, h463, h467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h388, h464, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                        · linarith only [h386, h389, h521, hlam]
                        · linarith only [h463, h520, h521, hlam]
                      · linarith only [h388, h520, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h387, h462, hlam]
                · linarith only [h0, h385, h460, h461, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h460, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
            · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
              · rcases m.htr 1 2 4 (by decide) (by decide) with h530 | h530
                · rcases m.htr 1 2 5 (by decide) (by decide) with h531 | h531
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h532 | h532
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h533 | h533
                      · linarith only [h385, h388, h533, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
                        · linarith only [h532, h533, h535, hlam]
                        · linarith only [h528, h535, hc14, hlam, hphi, u4elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h538 | h538
                      · linarith only [h388, h532, h538, hc03, hlam, hphi, ht34, u4elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h541 | h541
                          · linarith only [h529, h532, h541, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                            · linarith only [h388, h543, hc03, hlam, hphi, u3elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h545 | h545
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h546 | h546
                                · rcases h1bigk with h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h0, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    rcases p547_3 (m.d 0 1) (by simp) with h550 | h550
                                    · rcases p547_3 (m.d 1 2) (by simp) with h551 | h551
                                      · rcases p547_3 (m.d 1 3) (by simp) with h552 | h552
                                        · linarith only [h552, hlam, p547_0]
                                        · rcases p547_3 (m.d 1 4) (by simp) with h554 | h554
                                          · linarith only [h386, h554, hlam]
                                          · linarith only [h532, h554, hlam]
                                      · linarith only [h529, h551, hlam]
                                    · linarith only [h550, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h0, h540, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    rcases p547_3 (m.d 0 1) (by simp) with h560 | h560
                                    · rcases p547_3 (m.d 1 2) (by simp) with h561 | h561
                                      · rcases p547_3 (m.d 1 3) (by simp) with h562 | h562
                                        · linarith only [h385, h562, hlam]
                                        · rcases p547_3 (m.d 1 4) (by simp) with h564 | h564
                                          · linarith only [h386, h564, hlam]
                                          · linarith only [h540, h564, hlam]
                                      · linarith only [h531, h561, hlam]
                                    · linarith only [h560, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h386, h530, h545, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    rcases p547_3 (m.d 0 1) (by simp) with h571 | h571
                                    · linarith only [h0, h571, hlam]
                                    · linarith only [h385, h571, hlam]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    rcases p547_3 (m.d 0 1) (by simp) with h574 | h574
                                    · linarith only [h0, h574, hlam]
                                    · linarith only [h386, h574, hlam]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    rcases p547_3 (m.d 0 1) (by simp) with h577 | h577
                                    · linarith only [h0, h577, hlam]
                                    · linarith only [h387, h577, hlam]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h385, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h529, hlam, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h532, hlam, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h538, hlam, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h386, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h530, hlam, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h386, h529, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1, u0elo0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h0, h386, h531, h543, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h387, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h531, hlam, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h0, h387, h529, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p547_1]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [h540, hlam, p547_0]
                                  · have p547_0 := h547c.1
                                    have p547_1 := h547c.2.1
                                    have p547_2 := h547c.2.2.1
                                    have p547_3 := h547c.2.2.2
                                    linarith only [hlam, p547_0]
                                · linarith only [h528, h532, h546, hc14, hlam, hphi, u4elo0]
                              · linarith only [h540, h545, hc24, hlam, hphi, u4elo1]
                        · linarith only [h528, h540, hc14, hlam, hphi, u4elo0]
                  · linarith only [h0, h387, h531, hlam]
                · linarith only [h0, h530, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h385, h529, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
              · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h605 | h605
                      · linarith only [h385, h388, h605, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h607 | h607
                        · linarith only [h528, h607, hc04, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h609 | h609
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h610 | h610
                            · linarith only [h385, h388, h601, h610, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h612 | h612
                              · linarith only [h385, h386, h388, h528, h601, h602, h609, h612, hc34, hlam, hphi, u4elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                                · linarith only [h385, h528, h601, h609, h614, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h385, h388, h604, h614, hc34, hlam, hphi, u4elo4]
                          · linarith only [h385, h388, h604, h609, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h618 | h618
                      · linarith only [h388, h618, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
                        · linarith only [h386, h528, h620, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                          · linarith only [h601, h604, h622, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h624 | h624
                            · linarith only [h385, h388, h601, h624, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
                              · linarith only [h386, h528, h602, h626, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                                · linarith only [h528, h628, hc04, hlam, hphi, u4elo3]
                                · linarith only [h601, h604, h628, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h0, h387, h603, hlam]
                · linarith only [h0, h385, h601, h602, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h601, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h634 | h634
          · linarith only [h385, h387, h634, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h636 | h636
            · linarith only [h386, h387, h636, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h638 | h638
              · rcases m.htr 1 2 4 (by decide) (by decide) with h639 | h639
                · rcases m.htr 1 2 5 (by decide) (by decide) with h640 | h640
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                    · linarith only [h385, h387, h636, h641, hc34, hlam, hphi, u4elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                      · linarith only [h386, h387, h634, h636, h641, h643, hc03, hlam, hphi, ht34, u4elo4]
                      · linarith only [h386, h387, h641, h643, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
                    · linarith only [h0, h385, h640, h646, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
                      · linarith only [h0, h386, h640, h646, h648, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h386, h638, h640, h646, h648, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h639, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h385, h638, hc13, hlam, hphi, u3elo2]
      · linarith only [h385, h386, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h654 | h654
      · rcases m.htr 0 1 5 (by decide) (by decide) with h655 | h655
        · rcases m.htr 0 3 5 (by decide) (by decide) with h656 | h656
          · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
            · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
              · rcases m.htr 1 2 4 (by decide) (by decide) with h659 | h659
                · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h662 | h662
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h663 | h663
                        · linarith only [h385, h654, h663, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h385, h654, h657, h663, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h385, h662, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h661, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h385, h655, h658, h660, hlam]
                · linarith only [h385, h658, h659, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h654, h658, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h671 | h671
              · rcases m.htr 1 2 4 (by decide) (by decide) with h672 | h672
                · rcases m.htr 1 2 5 (by decide) (by decide) with h673 | h673
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h676 | h676
                        · linarith only [h654, h657, h676, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h678 | h678
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h679 | h679
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                              · linarith only [h657, h680, hc04, hlam, hphi, u4elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h682 | h682
                                · linarith only [h654, h657, h672, h678, h682, hlam]
                                · rcases h1bigk with h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h0, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h385, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h385, h672, h678, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p684_1, u3elo1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h385, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    rcases p684_3 (m.d 0 1) (by simp) with h690 | h690
                                    · linarith only [h690, hlam, p684_0]
                                    · rcases p684_3 (m.d 1 2) (by simp) with h692 | h692
                                      · rcases p684_3 (m.d 1 3) (by simp) with h693 | h693
                                        · linarith only [h671, h693, hlam]
                                        · linarith only [h385, h693, hlam]
                                      · linarith only [h692, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h385, hc01, hc12, hlam, hphi, p684_1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    rcases p684_3 (m.d 0 1) (by simp) with h699 | h699
                                    · linarith only [h0, h699, hlam]
                                    · linarith only [h654, h699, hlam]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    rcases p684_3 (m.d 0 1) (by simp) with h702 | h702
                                    · linarith only [h0, h702, hlam]
                                    · linarith only [h655, h702, hlam]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h655, h672, h676, h678, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p684_1, u3elo1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h671, hlam, p684_1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    rcases p684_3 (m.d 0 1) (by simp) with h708 | h708
                                    · linarith only [h385, h708, hlam]
                                    · linarith only [h654, h708, hlam]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    rcases p684_3 (m.d 0 1) (by simp) with h711 | h711
                                    · linarith only [h385, h711, hlam]
                                    · linarith only [h655, h711, hlam]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h654, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h672, hlam, p684_1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h674, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h676, hlam, p684_1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h655, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h673, hlam, p684_1]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h675, hlam, p684_0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [h655, h672, h678, hc34, hlam, hphi, ht0b, ht45, ht5b, p684_1, u0elo0]
                                  · have p684_0 := h684c.1
                                    have p684_1 := h684c.2.1
                                    have p684_2 := h684c.2.2.1
                                    have p684_3 := h684c.2.2.2
                                    linarith only [hlam, p684_0]
                            · linarith only [h385, h656, h679, hc23, hlam, hphi, u3elo1]
                          · linarith only [h674, h678, hc23, hlam, hphi, u3elo1]
                      · linarith only [h385, h654, h672, h675, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h385, h654, h672, h674, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h385, h655, h671, h673, hlam]
                · linarith only [h385, h671, h672, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h654, h671, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h385, h655, h656, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
          · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
            · linarith only [h654, h655, h733, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
              · rcases m.htr 1 2 4 (by decide) (by decide) with h736 | h736
                · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h740 | h740
                        · linarith only [h654, h733, h740, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h654, h655, h738, h740, hc34, hlam, hphi, u4elo4]
                      · linarith only [h385, h732, h739, hlam]
                    · linarith only [h385, h738, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h746 | h746
                      · linarith only [h735, h737, h746, hlam]
                      · linarith only [h385, h732, h746, hlam]
                    · linarith only [h385, h654, h736, h745, hc24, hlam, hphi, u4elo3]
                · linarith only [h735, h736, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h654, h735, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
            · linarith only [h654, h655, h752, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h754 | h754
              · rcases m.htr 1 2 4 (by decide) (by decide) with h755 | h755
                · rcases m.htr 1 2 5 (by decide) (by decide) with h756 | h756
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h757 | h757
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h758 | h758
                      · linarith only [h732, h758, hc03, hlam, hphi, u3elo1]
                      · linarith only [h385, h654, h755, h758, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h385, h654, h755, h757, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h763 | h763
                      · linarith only [h385, h654, h732, h754, h755, h756, h763, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h385, h654, h755, h763, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h385, h654, h755, h762, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h754, h755, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h754, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h769 | h769
        · rcases m.htr 0 3 5 (by decide) (by decide) with h770 | h770
          · rcases m.htr 0 4 5 (by decide) (by decide) with h771 | h771
            · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
              · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
                · rcases m.htr 1 2 5 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h776 | h776
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h777 | h777
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h780 | h780
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h781 | h781
                                · rcases h1bigk with h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c | h782c
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h0, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h385, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h654, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h654, h774, h779, h781, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p782_1, u4elo1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    rcases p782_3 (m.d 0 1) (by simp) with h788 | h788
                                    · linarith only [h788, hlam, p782_0]
                                    · rcases p782_3 (m.d 1 2) (by simp) with h790 | h790
                                      · rcases p782_3 (m.d 1 3) (by simp) with h791 | h791
                                        · linarith only [h772, h791, hlam]
                                        · linarith only [h385, h791, hlam]
                                      · linarith only [h790, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h654, h775, hc01, hc12, hlam, hphi, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h654, h769, h774, h779, h781, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    rcases p782_3 (m.d 0 1) (by simp) with h798 | h798
                                    · linarith only [h0, h798, hlam]
                                    · linarith only [h769, h798, hlam]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h769, h774, h779, h781, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p782_1, u3elo1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h772, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h654, h769, h774, h779, h781, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p782_1, u3elo1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    rcases p782_3 (m.d 0 1) (by simp) with h805 | h805
                                    · linarith only [h385, h805, hlam]
                                    · linarith only [h769, h805, hlam]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h769, h774, h779, h781, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p782_1, u4elo1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h773, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h775, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    rcases p782_3 (m.d 0 1) (by simp) with h812 | h812
                                    · linarith only [h654, h812, hlam]
                                    · linarith only [h769, h812, hlam]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h769, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h774, hlam, p782_1]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h776, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [h777, hlam, p782_0]
                                  · have p782_0 := h782c.1
                                    have p782_1 := h782c.2.1
                                    have p782_2 := h782c.2.2.1
                                    have p782_3 := h782c.2.2.2
                                    linarith only [hlam, p782_0]
                                · linarith only [h771, h781, hc34, hlam, hphi, u4elo0]
                              · linarith only [h385, h769, h777, h780, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h770, h779, hc23, hlam, hphi, u3elo0]
                          · linarith only [h775, h778, hc23, hlam, hphi, u3elo1]
                        · linarith only [h654, h769, h774, h777, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                      · linarith only [h385, h769, h774, h776, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h385, h769, h774, h775, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h385, h769, h774, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h773, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h769, h772, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h654, h769, h771, hlam]
          · linarith only [h385, h769, h770, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h832 | h832
          · rcases m.htr 0 4 5 (by decide) (by decide) with h833 | h833
            · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
              · rcases m.htr 1 2 4 (by decide) (by decide) with h835 | h835
                · rcases m.htr 1 2 5 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                                · rcases h1bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h0, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h385, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h654, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h769, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    rcases p844_3 (m.d 0 1) (by simp) with h850 | h850
                                    · linarith only [h850, hlam, p844_0]
                                    · rcases p844_3 (m.d 1 2) (by simp) with h852 | h852
                                      · rcases p844_3 (m.d 1 3) (by simp) with h853 | h853
                                        · linarith only [h834, h853, hlam]
                                        · linarith only [h385, h853, hlam]
                                      · linarith only [h852, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h385, hc01, hc12, hlam, hphi, p844_1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h654, hc01, hc12, hlam, hphi, p844_1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h769, hc01, hc12, hlam, hphi, p844_1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p844_1, u3elo1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h834, hlam, p844_1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h654, hc01, hlam, hphi, ht12, ht23, p844_1, u3elo1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h769, hc01, hlam, hphi, ht12, ht23, p844_1, u3elo1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p844_1, u4elo1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h835, hlam, p844_1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h837, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h769, hc01, hlam, hphi, ht12, ht23, ht34, p844_1, u4elo1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h838, hc01, hlam, hphi, ht12, ht23, p844_1, u3elo1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h836, hlam, p844_1]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h838, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [h839, hlam, p844_0]
                                  · have p844_0 := h844c.1
                                    have p844_1 := h844c.2.1
                                    have p844_2 := h844c.2.2.1
                                    have p844_3 := h844c.2.2.2
                                    linarith only [hlam, p844_0]
                                · linarith only [h833, h843, hc34, hlam, hphi, u4elo0]
                              · linarith only [h654, h833, h842, hc24, hlam, hphi, u4elo1]
                            · linarith only [h832, h840, h841, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h837, h840, hc23, hlam, hphi, u3elo1]
                        · linarith only [h654, h833, h839, hlam]
                      · linarith only [h385, h838, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h837, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h883 | h883
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h884 | h884
                      · linarith only [h834, h836, h884, hlam]
                      · linarith only [h385, h832, h884, hlam]
                    · linarith only [h385, h883, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h835, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h834, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h890 | h890
              · rcases m.htr 1 2 4 (by decide) (by decide) with h891 | h891
                · rcases m.htr 1 2 5 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h893 | h893
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h894 | h894
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h895 | h895
                        · linarith only [h833, h895, hc04, hlam, hphi, u4elo1]
                        · linarith only [h654, h895, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h385, h894, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h893, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
                      · linarith only [h890, h892, h901, hlam]
                      · linarith only [h654, h832, h900, h901, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h385, h900, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h385, h890, h891, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h890, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h907 | h907
            · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
              · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
                · rcases m.htr 1 2 5 (by decide) (by decide) with h910 | h910
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h911 | h911
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h912 | h912
                      · linarith only [h832, h912, hc03, hlam, hphi, u3elo1]
                      · linarith only [h385, h912, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h911, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h916 | h916
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h917 | h917
                      · linarith only [h385, h832, h908, h910, h917, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h385, h917, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h916, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h908, h909, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h908, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h923 | h923
              · rcases m.htr 1 2 4 (by decide) (by decide) with h924 | h924
                · rcases m.htr 1 2 5 (by decide) (by decide) with h925 | h925
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h927 | h927
                      · linarith only [h385, h832, h927, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h385, h927, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h926, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h931 | h931
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h932 | h932
                      · linarith only [h385, h832, h923, h925, h932, hc01, hc25, hlam, hphi, ht12]
                      · linarith only [h385, h932, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h385, h931, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h923, h924, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h923, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
