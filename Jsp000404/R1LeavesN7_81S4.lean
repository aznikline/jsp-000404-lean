import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_0_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h4, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                          · linarith only [h16, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                            · linarith only [h10, h18, h8, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                              · linarith only [h0, h10, h14, h20, h4, h6, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi6]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                                · linarith only [h0, h16, h22, h9, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                                  · linarith only [h0, h10, h16, h24, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h10, h24, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h28, h4, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h1, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h0, h30, h31, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h1, h34, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                          · linarith only [h0, h30, h36, h4, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                            · linarith only [h0, h30, h38, h4, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h38, h4, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
                · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                      · linarith only [h0, h42, h43, h45, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
                        · linarith only [h1, h47, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h42, h47, h6, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h43, h44, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h0, h4, h43, h51, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                      · linarith only [h42, h53, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                        · linarith only [h1, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h42, h55, h6, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                      · linarith only [h1, h6, h60, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                        · linarith only [h1, h42, h62, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi5]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                          · linarith only [h0, h59, h64, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                            · linarith only [h1, h58, h6, h66, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h1, h58, h68, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                                · linarith only [h0, h59, h70, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                                  · rcases h3bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h42, hc13, hlam, hphi, ht34, ht45, p73_1, u5elo3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h42, hc23, hlam, hphi, ht34, ht45, p73_1, u5elo3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h6, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h42, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h1, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p73_1, u1elo0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h60, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h62, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h4, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h58, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h66, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h68, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      rcases p73_3 (m.d 0 3) (by simp) with h89 | h89
                                      · linarith only [h89, hlam, p73_0]
                                      · rcases p73_3 (m.d 1 3) (by simp) with h91 | h91
                                        · linarith only [h60, h91, hlam]
                                        · rcases p73_3 (m.d 2 3) (by simp) with h93 | h93
                                          · linarith only [h66, h93, hlam]
                                          · rcases p73_3 (m.d 3 4) (by simp) with h95 | h95
                                            · rcases p73_3 (m.d 3 5) (by simp) with h96 | h96
                                              · linarith only [h72, h96, hlam]
                                              · linarith only [h42, h96, hlam]
                                            · linarith only [h95, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      rcases p73_3 (m.d 0 3) (by simp) with h100 | h100
                                      · linarith only [h100, h6, hlam]
                                      · linarith only [h1, h100, hlam]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      rcases p73_3 (m.d 0 3) (by simp) with h103 | h103
                                      · linarith only [h103, h6, hlam]
                                      · linarith only [h103, h4, hlam]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h42, hc03, hc34, hlam, hphi, p73_1]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc03, hlam, hphi, ht34, ht45, p73_1, u5elo3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h58, hc23, hlam, hphi, ht34, ht45, p73_1, u5elo3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht34, ht45, p73_1, u5elo3]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [h72, hlam, p73_0]
                                    · have p73_0 := h73c.1
                                      have p73_1 := h73c.2.1
                                      have p73_2 := h73c.2.2.1
                                      have p73_3 := h73c.2.2.2
                                      linarith only [hlam, p73_0]
                                  · linarith only [h1, h58, h6, h72, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h5, h58, h59, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h4, h42, h58, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
              · linarith only [h116, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
                    · linarith only [h0, h120, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                      · linarith only [h116, h118, h122, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                        · linarith only [h119, h120, h124, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h116, h118, h124, hc13, hc34, hlam, hphi]
                  · linarith only [h119, h4, h5, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                    · linarith only [h0, h129, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                      · linarith only [h1, h116, h118, h131, hc04, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                        · linarith only [h1, h118, h133, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                          · linarith only [h135, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · linarith only [h128, h129, h135, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h128, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 0 3 4 (by decide) (by decide) with h140 | h140
              · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
                · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
                  · linarith only [h139, h142, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                        · linarith only [h1, h146, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h145, h146, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h1, h140, h142, h144, h145, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h139, h144, h4, hc12, hc23, hlam, hphi]
                · linarith only [h140, h141, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h139, h140, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h153 | h153
              · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
                · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                  · linarith only [h0, h155, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                    · linarith only [h0, h139, h157, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h1, h160, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h154, h159, h160, hc34, hlam, hphi, ht45, u5elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                        · linarith only [h1, h153, h159, h163, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h1, h153, h159, h165, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h169 | h169
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                                  · linarith only [h1, h153, h165, h170, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · linarith only [h155, h159, h169, h170, hc12, hc24, hlam, hphi]
                                · linarith only [h139, h169, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                              · linarith only [h0, h168, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h153, h167, h4, hlam]
                · linarith only [h153, h154, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                  · linarith only [h177, h178, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                    · linarith only [h0, h139, h180, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                      · linarith only [h1, h153, h177, h182, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                        · linarith only [h182, h184, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · linarith only [h153, h177, h178, h184, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                  · linarith only [h0, h187, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
                    · linarith only [h0, h139, h189, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                      · linarith only [h1, h153, h191, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                        · linarith only [h1, h177, h193, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi5]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                          · linarith only [h195, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                                  · linarith only [h189, h195, h197, h200, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h153, h199, h200, h4, hc12, hc24, hlam, hphi]
                                · linarith only [h0, h139, h199, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                              · linarith only [h0, h198, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                              · linarith only [h0, h177, h197, h205, h4, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h205, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h209 | h209
        · linarith only [h2, h209, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
        · linarith only [h1, h209, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h212 | h212
      · rcases m.htr 0 1 5 (by decide) (by decide) with h213 | h213
        · linarith only [h1, h213, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
        · linarith only [h212, h213, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h216 | h216
        · linarith only [h212, h216, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
        · linarith only [h0, h216, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h219 | h219
    · rcases m.htr 0 1 4 (by decide) (by decide) with h220 | h220
      · rcases m.htr 0 1 5 (by decide) (by decide) with h221 | h221
        · linarith only [h0, h221, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · linarith only [h219, h221, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h224 | h224
        · linarith only [h0, h224, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · linarith only [h219, h224, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h227 | h227
      · rcases m.htr 0 1 5 (by decide) (by decide) with h228 | h228
        · linarith only [h0, h228, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · linarith only [h227, h228, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h231 | h231
        · linarith only [h0, h231, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h233 | h233
          · rcases m.htr 0 2 4 (by decide) (by decide) with h234 | h234
            · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
              · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
                · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                              · linarith only [h0, h233, h243, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                              · linarith only [h219, h236, h242, h243, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                              · linarith only [h227, h235, h242, h246, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                                · linarith only [h0, h233, h235, h242, h248, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                                  · linarith only [h0, h233, h235, h242, h248, h250, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · linarith only [h237, h239, h241, h242, h250, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h227, h241, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h219, h233, h236, h240, hc01, hlam, hphi, u1elo1]
                      · linarith only [h219, h235, h239, hlam]
                    · linarith only [h0, h234, h238, hlam]
                  · linarith only [h0, h233, h237, hlam]
                · linarith only [h235, h236, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h259 | h259
                · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h262 | h262
                      · linarith only [h235, h259, h262, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                            · linarith only [h0, h233, h262, h266, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                              · linarith only [h0, h234, h266, h268, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                              · linarith only [h219, h259, h262, h268, hc23, hc34, hlam, hphi]
                          · linarith only [h227, h235, h259, h265, hlam, hphi, u5ehi8, u5elo4]
                        · linarith only [h219, h227, h235, h259, h264, hc01, hlam, hphi, u1elo3]
                    · linarith only [h0, h234, h261, hlam]
                  · linarith only [h0, h233, h260, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                      · linarith only [h219, h235, h277, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                        · linarith only [h219, h259, h277, h279, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h219, h279, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h234, h276, hlam]
                  · linarith only [h0, h219, h233, h275, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
              · linarith only [h233, h234, h284, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                    · linarith only [h233, h234, h286, h288, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                      · linarith only [h284, h286, h287, h288, h290, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h292 | h292
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                            · linarith only [h0, h233, h288, h290, h294, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                              · linarith only [h0, h233, h288, h294, h296, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                              · linarith only [h0, h233, h286, h288, h294, h296, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h233, h286, h288, h293, hlam, hphi, u5ehi8, u5elo4]
                        · linarith only [h219, h286, h292, hlam]
                  · linarith only [h0, h233, h287, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
                    · linarith only [h233, h234, h303, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
                      · linarith only [h219, h284, h305, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                        · linarith only [h219, h286, h305, h307, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h219, h307, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h233, h302, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h311 | h311
            · rcases m.htr 0 3 4 (by decide) (by decide) with h312 | h312
              · rcases m.htr 0 3 5 (by decide) (by decide) with h313 | h313
                · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
                  · linarith only [h233, h311, h314, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h322 | h322
                                · linarith only [h0, h311, h314, h322, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                                  · linarith only [h320, h322, h324, hlam]
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
                                      linarith only [h219, hlam, p326_1]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h233, hlam, p326_1]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      rcases p326_3 (m.d 0 3) (by simp) with h330 | h330
                                      · rcases p326_3 (m.d 1 3) (by simp) with h331 | h331
                                        · rcases p326_3 (m.d 2 3) (by simp) with h332 | h332
                                          · rcases p326_3 (m.d 3 4) (by simp) with h333 | h333
                                            · linarith only [h333, hlam, p326_0]
                                            · rcases p326_3 (m.d 3 5) (by simp) with h335 | h335
                                              · linarith only [h313, h335, hlam]
                                              · linarith only [h324, h335, hlam]
                                          · linarith only [h320, h332, hlam]
                                        · linarith only [h317, h331, hlam]
                                      · linarith only [h330, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h219, hlam, hphi, ht01, ht0b, ht5b, p326_1, u1elo2, u5ehi8]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h219, hc01, hlam, hphi, p326_1, u1elo2]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h314, hlam, p326_1]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      rcases p326_3 (m.d 0 3) (by simp) with h345 | h345
                                      · linarith only [h219, h345, hlam]
                                      · linarith only [h312, h345, hlam]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p326_1, u1elo2, u5ehi8]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h313, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p326_1, u5ehi8]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h219, hc01, hc23, hlam, hphi, ht12, p326_1]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h314, h316, h319, h320, h322, hlam, p326_2]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      rcases p326_3 (m.d 0 3) (by simp) with h353 | h353
                                      · linarith only [h233, h353, hlam]
                                      · linarith only [h313, h353, hlam]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h312, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h317, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h320, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h324, hlam, p326_1]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h313, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h318, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [h321, hlam, p326_0]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht45, p326_1, u5elo3]
                                    · have p326_0 := h326c.1
                                      have p326_1 := h326c.2.1
                                      have p326_2 := h326c.2.2.1
                                      have p326_3 := h326c.2.2.2
                                      linarith only [hlam, p326_0]
                              · linarith only [h219, h313, h314, h321, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                            · linarith only [h314, h316, h319, h320, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                          · linarith only [h227, h319, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h219, h313, h318, hlam]
                      · linarith only [h219, h312, h317, hlam]
                    · linarith only [h0, h311, h316, hlam]
                · linarith only [h312, h313, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h233, h311, h312, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 3 5 (by decide) (by decide) with h375 | h375
                · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                  · linarith only [h0, h233, h376, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
                    · linarith only [h0, h311, h376, h378, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h380 | h380
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h381 | h381
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h384 | h384
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h385 | h385
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                                  · linarith only [h219, h374, h386, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
                                  · rcases h3bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h219, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h233, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      rcases p388_3 (m.d 0 3) (by simp) with h392 | h392
                                      · rcases p388_3 (m.d 1 3) (by simp) with h393 | h393
                                        · rcases p388_3 (m.d 2 3) (by simp) with h394 | h394
                                          · rcases p388_3 (m.d 3 4) (by simp) with h395 | h395
                                            · linarith only [h395, hlam, p388_0]
                                            · rcases p388_3 (m.d 3 5) (by simp) with h397 | h397
                                              · linarith only [h375, h397, hlam]
                                              · linarith only [h386, h397, hlam]
                                          · linarith only [h383, h394, hlam]
                                        · linarith only [h380, h393, hlam]
                                      · linarith only [h392, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h219, hlam, hphi, ht01, ht0b, ht5b, p388_1, u1elo2, u5ehi8]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h219, hc01, hlam, hphi, p388_1, u1elo2]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h376, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      rcases p388_3 (m.d 0 3) (by simp) with h407 | h407
                                      · linarith only [h219, h407, hlam]
                                      · linarith only [h374, h407, hlam]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p388_1, u1elo2, u5ehi8]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h375, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1, u5ehi8]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h380, h382, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p388_1, u5ehi9]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      rcases p388_3 (m.d 0 3) (by simp) with h414 | h414
                                      · linarith only [h233, h414, hlam]
                                      · linarith only [h374, h414, hlam]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      rcases p388_3 (m.d 0 3) (by simp) with h417 | h417
                                      · linarith only [h233, h417, hlam]
                                      · linarith only [h375, h417, hlam]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h374, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h380, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h383, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h386, hlam, p388_1]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h375, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h381, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [h384, hlam, p388_0]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht45, p388_1, u5elo3]
                                    · have p388_0 := h388c.1
                                      have p388_1 := h388c.2.1
                                      have p388_2 := h388c.2.2.1
                                      have p388_3 := h388c.2.2.2
                                      linarith only [hlam, p388_0]
                                · linarith only [h378, h380, h382, h385, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h0, h219, h233, h375, h384, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h376, h383, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h227, h382, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h219, h375, h381, hlam]
                      · linarith only [h219, h227, h374, h375, h380, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi8]
                · linarith only [h374, h375, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h437 | h437
                · rcases m.htr 1 2 3 (by decide) (by decide) with h438 | h438
                  · linarith only [h0, h233, h438, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
                    · linarith only [h0, h311, h440, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                      · linarith only [h374, h437, h442, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h444 | h444
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                            · linarith only [h0, h438, h442, h446, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h438, h446, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h227, h445, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h219, h437, h444, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
                  · linarith only [h0, h233, h451, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h453 | h453
                    · linarith only [h0, h311, h451, h453, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                      · linarith only [h219, h374, h455, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
                        · linarith only [h0, h233, h437, h455, h457, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h451, h457, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]

theorem r1l7_11_13_25_L_I_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h11, h13, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h13, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h12, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h11, h4, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h9, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h4, h5, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h5, h6, hlam]
                  · linarith only [h23, h4, hc13, hlam, hphi, u3elo0]
                · linarith only [h22, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                            · linarith only [h27, h32, h34, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h34, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h33, h5, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h32, h5, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h31, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h27, h30, h5, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h27, h29, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h27, h28, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                            · rcases h1bigk with h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h52 | h52
                                · rcases p50_3 (m.d 1 2) (by simp) with h53 | h53
                                  · linarith only [h53, hlam, p50_0]
                                  · rcases p50_3 (m.d 1 3) (by simp) with h55 | h55
                                    · linarith only [h1, h55, hlam]
                                    · linarith only [h5, h55, hlam]
                                · linarith only [h52, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h44, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h60 | h60
                                · rcases p50_3 (m.d 1 2) (by simp) with h61 | h61
                                  · linarith only [h0, h61, hlam]
                                  · rcases p50_3 (m.d 1 3) (by simp) with h63 | h63
                                    · linarith only [h1, h63, hlam]
                                    · linarith only [h44, h63, hlam]
                                · linarith only [h60, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h67 | h67
                                · rcases p50_3 (m.d 1 2) (by simp) with h68 | h68
                                  · linarith only [h0, h68, hlam]
                                  · linarith only [h43, h68, hlam]
                                · linarith only [h67, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h0, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h5, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h27, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h27, h43, h47, h48, h49, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p50_1, u3elo2]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h1, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, p50_1, u3elo1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h1, h27, h43, h48, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h81 | h81
                                · rcases p50_3 (m.d 1 2) (by simp) with h82 | h82
                                  · linarith only [h5, h82, hlam]
                                  · linarith only [h43, h82, hlam]
                                · linarith only [h3, h81, hlam]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h2, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h2, h43, h48, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h44, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h90 | h90
                                · rcases p50_3 (m.d 1 2) (by simp) with h91 | h91
                                  · linarith only [h27, h91, hlam]
                                  · linarith only [h43, h91, hlam]
                                · linarith only [h3, h90, hlam]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h3, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h43, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h45, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h46, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                            · linarith only [h49, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h48, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h47, h5, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h46, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h45, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h4, h43, h44, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                · linarith only [h43, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
            · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
              · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · linarith only [h110, h4, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                        · linarith only [h0, h107, h110, h112, h114, h2, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                            · rcases h1bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h107, h116, h117, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                rcases p118_3 (m.d 0 1) (by simp) with h121 | h121
                                · rcases p118_3 (m.d 1 2) (by simp) with h122 | h122
                                  · linarith only [h0, h122, hlam]
                                  · linarith only [h107, h122, hlam]
                                · linarith only [h121, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                rcases p118_3 (m.d 0 1) (by simp) with h126 | h126
                                · rcases p118_3 (m.d 1 2) (by simp) with h127 | h127
                                  · linarith only [h0, h127, hlam]
                                  · linarith only [h108, h127, hlam]
                                · linarith only [h126, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                rcases p118_3 (m.d 0 1) (by simp) with h131 | h131
                                · rcases p118_3 (m.d 1 2) (by simp) with h132 | h132
                                  · linarith only [h0, h132, hlam]
                                  · linarith only [h109, h132, hlam]
                                · linarith only [h131, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h0, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h0, h107, h116, h117, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h0, h107, h110, h116, h117, hc01, hc45, hlam, hphi, ht0b, ht5b, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                rcases p118_3 (m.d 0 1) (by simp) with h140 | h140
                                · rcases p118_3 (m.d 1 2) (by simp) with h141 | h141
                                  · rcases p118_3 (m.d 1 3) (by simp) with h142 | h142
                                    · linarith only [h107, h142, hlam]
                                    · linarith only [h112, h142, hlam]
                                  · linarith only [h109, h141, hlam]
                                · linarith only [h140, h3, hlam]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h1, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h107, hlam, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h110, hlam, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h1, h109, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1, u3elo3]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h2, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h108, hlam, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h2, h4, hc13, hlam, hphi, p118_1, u3elo3]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                rcases p118_3 (m.d 0 1) (by simp) with h156 | h156
                                · rcases p118_3 (m.d 1 2) (by simp) with h157 | h157
                                  · rcases p118_3 (m.d 1 3) (by simp) with h158 | h158
                                    · linarith only [h110, h158, hlam]
                                    · linarith only [h112, h158, hlam]
                                  · linarith only [h109, h157, hlam]
                                · linarith only [h156, h3, hlam]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h3, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h109, hlam, p118_1]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h112, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [h113, hlam, p118_0]
                              · have p118_0 := h118c.1
                                have p118_1 := h118c.2.1
                                have p118_2 := h118c.2.2.1
                                have p118_3 := h118c.2.2.2
                                linarith only [hlam, p118_0]
                            · linarith only [h117, h4, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h1, h112, h116, h4, hc23, hlam, hphi, u3elo3]
                      · linarith only [h110, h113, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h107, h112, hc23, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h109, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                  · linarith only [h174, h4, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                        · linarith only [h1, h107, h108, h176, h178, h2, h4, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h107, h108, h178, hc23, hlam, hphi, u3elo3]
                      · linarith only [h177, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h176, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h107, h173, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
              · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                  · linarith only [h186, h4, hc03, hlam, hphi, u3elo1]
                  · linarith only [h107, h184, h186, hlam]
                · linarith only [h184, h185, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                  · linarith only [h1, h191, h4, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                        · linarith only [h195, h4, hc03, hlam, hphi, u3elo2]
                        · linarith only [h107, h190, h195, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h107, h190, h191, h194, hc25, hlam, hphi, u5elo4]
                    · linarith only [h107, h190, h193, hc25, hlam, hphi, u5elo3]
                · linarith only [h190, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h202 | h202
        · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
          · linarith only [h1, h2, h203, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
            · linarith only [h0, h2, h203, h205, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
              · linarith only [h1, h2, h205, h207, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                  · linarith only [h1, h2, h203, h210, hlam]
                  · linarith only [h1, h2, h205, h210, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h209, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h202, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h216 | h216
    · rcases m.htr 0 1 4 (by decide) (by decide) with h217 | h217
      · rcases m.htr 0 1 5 (by decide) (by decide) with h218 | h218
        · rcases m.htr 0 3 4 (by decide) (by decide) with h219 | h219
          · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                            · linarith only [h0, h216, h220, h226, h228, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h228, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h227, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h219, h226, hc23, hlam, hphi, u3elo0]
                      · linarith only [h225, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h224, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h219, h220, h223, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h222, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h217, h221, hlam]
            · linarith only [h0, h220, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h239 | h239
            · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
              · rcases m.htr 1 2 5 (by decide) (by decide) with h241 | h241
                · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h216, h219, h242, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                        · linarith only [h216, h219, h239, h246, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                            · rcases h1bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h0, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h0, h239, h248, h249, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h0, h239, h242, h248, h249, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                rcases p250_3 (m.d 0 1) (by simp) with h255 | h255
                                · rcases p250_3 (m.d 1 2) (by simp) with h256 | h256
                                  · rcases p250_3 (m.d 1 3) (by simp) with h257 | h257
                                    · linarith only [h216, h257, hlam]
                                    · linarith only [h244, h257, hlam]
                                  · linarith only [h241, h256, hlam]
                                · linarith only [h255, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h216, h239, h248, h249, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                rcases p250_3 (m.d 0 1) (by simp) with h264 | h264
                                · linarith only [h0, h264, hlam]
                                · linarith only [h216, h264, hlam]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                rcases p250_3 (m.d 0 1) (by simp) with h267 | h267
                                · linarith only [h0, h267, hlam]
                                · linarith only [h217, h267, hlam]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                rcases p250_3 (m.d 0 1) (by simp) with h270 | h270
                                · linarith only [h0, h270, hlam]
                                · linarith only [h218, h270, hlam]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h216, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h239, hlam, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h242, hlam, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h0, h217, h242, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h217, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h240, hlam, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h0, h217, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h0, h217, h241, h248, h249, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h218, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h241, hlam, p250_1]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h244, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [h245, hlam, p250_0]
                              · have p250_0 := h250c.1
                                have p250_1 := h250c.2.1
                                have p250_2 := h250c.2.2.1
                                have p250_3 := h250c.2.2.2
                                linarith only [hlam, p250_0]
                            · linarith only [h219, h249, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h216, h219, h244, h248, hc23, hlam, hphi, u3elo3]
                      · linarith only [h245, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h244, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h241, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h217, h240, hlam]
            · linarith only [h0, h239, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h216, h218, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h296 | h296
        · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
          · linarith only [h216, h217, h297, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
            · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
              · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
                  · linarith only [h216, h217, h297, h300, h302, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h216, h217, h299, h302, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h301, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
                  · linarith only [h0, h216, h297, h300, h307, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h216, h299, h300, h307, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h216, h299, h306, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h299, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h216, h296, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h313 | h313
      · rcases m.htr 0 1 5 (by decide) (by decide) with h314 | h314
        · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
          · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
            · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
              · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
                · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                      · linarith only [h216, h313, h321, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h317, h321, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h216, h313, h317, h320, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h216, h313, h317, h319, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h216, h313, h316, h317, h318, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h216, h313, h316, h317, hlam]
            · linarith only [h0, h316, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h216, h313, h315, hlam]
        · linarith only [h313, h314, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h331 | h331
        · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
          · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
            · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
              · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h340 | h340
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h341 | h341
                            · rcases h1bigk with h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c | h342c
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h0, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h216, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h313, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h313, h335, h336, h340, h341, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p342_1, u3elo1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                rcases p342_3 (m.d 0 1) (by simp) with h348 | h348
                                · linarith only [h348, hlam, p342_0]
                                · rcases p342_3 (m.d 1 2) (by simp) with h350 | h350
                                  · rcases p342_3 (m.d 1 3) (by simp) with h351 | h351
                                    · linarith only [h333, h351, hlam]
                                    · linarith only [h216, h351, hlam]
                                  · linarith only [h350, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h313, h336, hc01, hc12, hlam, hphi, p342_1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h313, h331, h335, h340, h341, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p342_1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                rcases p342_3 (m.d 0 1) (by simp) with h358 | h358
                                · linarith only [h0, h358, hlam]
                                · linarith only [h331, h358, hlam]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h331, h335, h340, h341, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p342_1, u3elo1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h333, hlam, p342_1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h313, h331, h335, h340, h341, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p342_1, u3elo1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                rcases p342_3 (m.d 0 1) (by simp) with h365 | h365
                                · linarith only [h216, h365, hlam]
                                · linarith only [h331, h365, hlam]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h331, h335, h336, h340, h341, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p342_1, u3elo1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h334, hlam, p342_1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h336, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                rcases p342_3 (m.d 0 1) (by simp) with h372 | h372
                                · linarith only [h313, h372, hlam]
                                · linarith only [h331, h372, hlam]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h331, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h335, hlam, p342_1]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h337, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [h338, hlam, p342_0]
                              · have p342_0 := h342c.1
                                have p342_1 := h342c.2.1
                                have p342_2 := h342c.2.2.1
                                have p342_3 := h342c.2.2.2
                                linarith only [hlam, p342_0]
                            · linarith only [h341, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h340, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h216, h332, h339, hc23, hlam, hphi, u3elo1]
                      · linarith only [h313, h331, h335, h338, hc25, hlam, hphi, u5elo4]
                    · linarith only [h313, h331, h335, h336, h337, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                  · linarith only [h216, h331, h332, h335, h336, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h335, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                  · linarith only [h333, h334, h388, hlam]
                  · linarith only [h216, h332, h388, hlam]
                · linarith only [h216, h333, h387, hc03, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h333, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h393 | h393
            · rcases m.htr 1 2 4 (by decide) (by decide) with h394 | h394
              · rcases m.htr 1 2 5 (by decide) (by decide) with h395 | h395
                · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
                  · linarith only [h216, h331, h332, h395, h396, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h216, h331, h395, h396, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h216, h393, h395, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                  · linarith only [h216, h331, h332, h393, h394, h400, h401, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h216, h331, h400, h401, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h400, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h393, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h331, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_11_13_25_L_I_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h5, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h10, h8, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h8, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h16, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h4, h5, h7, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h5, h6, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h21, h23, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h23, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h20, h5, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                            · linarith only [h27, h32, h34, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                            · linarith only [h34, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h27, h32, h33, h5, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h28, h32, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h29, h31, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h30, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                  · linarith only [h27, h29, h5, hlam]
                · linarith only [h27, h28, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                            · linarith only [h1, h44, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h49, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h27, h43, h47, h48, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h43, h47, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h27, h43, h46, hlam, hphi, u5ehi7, u5elo4]
                    · linarith only [h44, h45, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h44, h56, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h56, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                            · linarith only [h1, h59, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h64, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h4, h43, h5, h60, h63, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
                        · linarith only [h5, h59, h62, hlam]
                      · linarith only [h59, h61, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h59, h60, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h59, h71, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h71, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
            · linarith only [h0, h4, h74, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
              · linarith only [h0, h4, h76, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                · linarith only [h0, h4, h78, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                            · linarith only [h1, h80, h85, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h85, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h74, h84, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                        · linarith only [h74, h80, h83, hlam]
                      · linarith only [h80, h82, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h80, h81, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                    · linarith only [h80, h92, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h92, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
        · linarith only [h1, h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
        · rcases m.htr 0 2 5 (by decide) (by decide) with h97 | h97
          · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
            · linarith only [h0, h2, h98, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
              · linarith only [h100, h2, h96, h98, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                · linarith only [h1, h102, h2, h98, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · linarith only [h0, h100, h102, h2, h97, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
            · linarith only [h0, h105, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
              · linarith only [h0, h107, h97, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                · linarith only [h0, h109, h97, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                  · linarith only [h1, h107, h111, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1, h111, h2, hc34, hlam, hphi, u3ehi1]
        · linarith only [h1, h96, hlam, hphi, ht34, ht45, u3ehi1, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h115 | h115
      · rcases m.htr 0 1 5 (by decide) (by decide) with h116 | h116
        · rcases m.htr 0 2 5 (by decide) (by decide) with h117 | h117
          · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
            · linarith only [h0, h1, h118, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                · linarith only [h0, h1, h118, h121, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                · linarith only [h120, h121, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                · linarith only [h0, h1, h124, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · linarith only [h0, h1, h117, h118, h124, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
            · linarith only [h0, h1, h127, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
              · linarith only [h0, h117, h129, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                · linarith only [h0, h117, h131, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                      · linarith only [h1, h115, h127, h135, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                      · linarith only [h133, h135, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h1, h134, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1, h116, h133, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
        · linarith only [h115, h116, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h141 | h141
        · rcases m.htr 0 2 5 (by decide) (by decide) with h142 | h142
          · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
            · linarith only [h0, h1, h143, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
              · linarith only [h0, h115, h145, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                · linarith only [h0, h1, h143, h147, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                · linarith only [h0, h1, h142, h143, h147, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
            · linarith only [h0, h1, h150, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
              · linarith only [h0, h142, h152, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
                · linarith only [h0, h142, h154, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                            · rcases h1bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h115, h150, h156, hc12, hc23, hlam, hphi, p162_1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h1, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h115, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h115, h150, h156, h157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p162_1, u3ehi4]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h150, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h152, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h154, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, h150, hc12, hc23, hlam, hphi, p162_1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                rcases p162_3 (m.d 0 1) (by simp) with h174 | h174
                                · linarith only [h1, h174, hlam]
                                · linarith only [h0, h174, hlam]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h115, h141, h150, h157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p162_1, u3ehi4]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                rcases p162_3 (m.d 0 1) (by simp) with h179 | h179
                                · linarith only [h1, h179, hlam]
                                · linarith only [h141, h179, hlam]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h141, h157, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u3ehi4]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                rcases p162_3 (m.d 0 1) (by simp) with h183 | h183
                                · linarith only [h115, h183, hlam]
                                · linarith only [h0, h183, hlam]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h156, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                rcases p162_3 (m.d 0 1) (by simp) with h188 | h188
                                · linarith only [h115, h188, hlam]
                                · linarith only [h141, h188, hlam]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h141, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p162_1, u5elo1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h157, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h158, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                            · linarith only [h161, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h115, h141, h150, h156, h157, h160, hlam]
                        · linarith only [h115, h141, h150, h156, h157, h159, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h115, h141, h157, h158, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h115, h141, h156, h157, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                  · linarith only [h1, h141, h156, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
        · linarith only [h0, h141, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h203 | h203
    · rcases m.htr 0 1 4 (by decide) (by decide) with h204 | h204
      · rcases m.htr 0 1 5 (by decide) (by decide) with h205 | h205
        · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
          · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
            · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
              · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                  · linarith only [h0, h203, h210, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h212 | h212
                    · linarith only [h0, h204, h210, h212, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h212, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h0, h205, h209, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h205, h208, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h203, h207, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h203, h206, hlam, hphi, ht34, ht45, u3ehi1, u5elo2]
        · linarith only [h203, h205, hlam, hphi, ht34, ht45, u3ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h220 | h220
        · rcases m.htr 0 2 5 (by decide) (by decide) with h221 | h221
          · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
            · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
              · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                  · linarith only [h203, h204, h223, h225, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h203, h204, h225, hc34, hlam, hphi, u3ehi1]
                · linarith only [h203, h204, h222, h223, h224, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h203, h223, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h203, h222, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h203, h221, hlam, hphi, ht34, ht45, u3ehi1, u5elo2]
        · linarith only [h203, h220, hlam, hphi, ht34, ht45, u3ehi1, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h233 | h233
      · rcases m.htr 0 1 5 (by decide) (by decide) with h234 | h234
        · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
          · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
            · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
              · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h240 | h240
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h241 | h241
                      · linarith only [h203, h233, h236, h241, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                      · linarith only [h239, h241, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h203, h234, h240, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                  · linarith only [h203, h234, h238, h239, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h203, h234, h236, h238, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h203, h234, h236, h237, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h234, h236, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h234, h235, hlam, hphi, u5ehi6, u5elo2]
        · linarith only [h233, h234, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h251 | h251
        · rcases m.htr 0 2 5 (by decide) (by decide) with h252 | h252
          · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
            · rcases m.htr 1 2 4 (by decide) (by decide) with h254 | h254
              · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
                            · linarith only [h253, h259, h261, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h261, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h260, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
                          · linarith only [h259, h265, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h265, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                      · linarith only [h233, h251, h258, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
                    · linarith only [h233, h251, h255, h256, h257, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h203, h251, h255, h256, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h0, h251, h255, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h203, h251, h253, h254, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h251, h253, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h251, h252, hlam, hphi, u5ehi6, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
          · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
            · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
              · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                            · linarith only [h276, h282, h284, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h284, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h283, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h288 | h288
                          · linarith only [h279, h282, h288, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · linarith only [h288, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                      · linarith only [h233, h281, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h280, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h293 | h293
                    · linarith only [h279, h293, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h293, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h0, h278, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h297 | h297
                · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                  · linarith only [h276, h277, h298, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                    · linarith only [h298, h300, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h300, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h0, h297, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
              · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                            · linarith only [h276, h304, h309, h311, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                            · linarith only [h311, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h276, h304, h308, h310, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                        · linarith only [h276, h304, h306, h309, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h306, h308, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h307, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                  · linarith only [h276, h304, h306, hlam]
                · linarith only [h0, h275, h305, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                            · rcases h1bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h0, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h203, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h233, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h251, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h304, hc01, hc24, hlam, hphi, ht12, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h276, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h304, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h304, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p327_1, u5ehi6]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 1) (by simp) with h338 | h338
                                · linarith only [h338, hlam, p327_0]
                                · rcases p327_3 (m.d 1 2) (by simp) with h340 | h340
                                  · linarith only [h276, h340, hlam]
                                  · linarith only [h0, h340, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h0, h275, h276, h304, h325, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p327_1, u3ehi4]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h251, h276, hc01, hc23, hlam, hphi, ht12, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 1) (by simp) with h347 | h347
                                · linarith only [h347, hlam, p327_0]
                                · rcases p327_3 (m.d 1 2) (by simp) with h349 | h349
                                  · linarith only [h304, h349, hlam]
                                  · linarith only [h0, h349, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h0, h275, h325, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p327_1, u3ehi4]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h321, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h251, h304, h324, hc01, hc23, hlam, hphi, ht12, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p327_1, u5elo1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h320, hlam, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h322, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h323, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                            · linarith only [h326, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h0, h275, h304, h324, h325, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h275, h276, h324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h233, h323, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h275, h304, h321, h322, hlam, hphi, u5ehi7, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
                    · linarith only [h321, h366, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h275, h276, h366, hlam, hphi, u5ehi7, u5elo3]
                · linarith only [h0, h275, h320, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
            · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
              · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h378 | h378
                            · linarith only [h370, h376, h378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · linarith only [h378, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                          · linarith only [h377, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                          · linarith only [h376, h382, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h382, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                      · linarith only [h233, h375, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h374, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h387 | h387
                    · linarith only [h373, h387, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h387, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h0, h372, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                · linarith only [h0, h275, h371, h391, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h391, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h394 | h394
              · rcases m.htr 1 2 5 (by decide) (by decide) with h395 | h395
                · linarith only [h0, h275, h370, h395, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h394, h395, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                · linarith only [h0, h275, h394, h398, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h398, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

end R2N4
