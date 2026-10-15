import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
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
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · linarith only [h0, h10, h15, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                                · linarith only [h0, h10, h18, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h18, h7, hc23, hlam, hphi, u3elo0]
                            · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h12, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                              · linarith only [h2, h29, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                                · linarith only [h0, h25, h31, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h28, h31, hc23, hlam, hphi, u3elo1]
                            · linarith only [h28, h7, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h27, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h25, h26, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h25, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                            · linarith only [h39, h44, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                                · linarith only [h39, h41, h47, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                                  · linarith only [h0, h42, h49, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h40, h47, h49, h7, hc23, hlam, hphi, u3elo3]
                              · linarith only [h39, h40, h44, h46, h7, hc13, hlam, hphi, u3elo3]
                          · linarith only [h43, h6, hc12, hlam, hphi, u2elo0]
                        · linarith only [h41, h42, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h41, hc12, hlam, hphi, u2elo0]
                    · linarith only [h39, h40, h7, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                            · linarith only [h61, h7, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h63 | h63
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                                · linarith only [h1, h58, h64, h7, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                                  · linarith only [h0, h59, h66, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h2, h63, h66, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h57, h58, h61, h63, h7, hc23, hlam, hphi, u3elo3]
                          · linarith only [h6, h60, hc12, hlam, hphi, u2elo0]
                        · linarith only [h5, h58, h59, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h58, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                            · linarith only [h1, h39, h76, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                              · linarith only [h2, h57, h78, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                                · linarith only [h1, h7, h73, h80, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                                  · linarith only [h1, h57, h7, h73, h74, h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                                    · linarith only [h1, h57, h7, h73, h84, hc23, hlam, hphi, u3elo3]
                                    · linarith only [h1, h7, h73, h84, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h6, h75, hc12, hlam, hphi, u2elo0]
                        · linarith only [h5, h73, h74, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h4, h73, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 0 3 4 (by decide) (by decide) with h92 | h92
                · linarith only [h4, h5, h92, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                        · linarith only [h0, h5, h97, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                            · linarith only [h1, h100, h92, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                                · linarith only [h0, h103, h92, h96, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h0, h103, h5, h96, hc23, hlam, hphi, u3elo3]
                              · linarith only [h102, h94, h95, h96, h97, hc23, hlam, hphi, u3elo0]
                          · linarith only [h96, h99, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h4, h5, h96, hc12, hlam, hphi, u2elo3]
                    · linarith only [h4, h5, h95, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                        · linarith only [h0, h112, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                            · linarith only [h1, h115, h94, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                                · linarith only [h0, h111, h118, h92, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h118, h4, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h110, h111, h112, h117, h92, hc23, hlam, hphi, u3elo3]
                          · linarith only [h111, h114, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h111, h4, h5, hc12, hlam, hphi, u2elo3]
                    · linarith only [h110, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h4, h91, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h126 | h126
            · rcases m.htr 0 2 5 (by decide) (by decide) with h127 | h127
              · rcases m.htr 0 3 4 (by decide) (by decide) with h128 | h128
                · rcases m.htr 0 3 5 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
                      · linarith only [h131, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                                  · linarith only [h0, h133, h138, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                  · linarith only [h126, h130, h137, h138, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · linarith only [h137, h4, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h126, h130, h136, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h128, h131, h133, h135, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h133, h134, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h126, h133, h4, hc12, hlam, hphi, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                      · linarith only [h146, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
                              · linarith only [h130, h151, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                                  · linarith only [h0, h130, h148, h154, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                                    · linarith only [h130, h148, h153, h156, h2, hlam]
                                    · rcases h0bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h0, h149, h154, hc24, hlam, hphi, ht0b, ht45, ht5b, p158_1, u0elo0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h1, h146, h149, h153, h154, hc34, hlam, hphi, ht0b, ht45, ht5b, p158_1, u0elo0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        rcases p158_3 (m.d 0 1) (by simp) with h162 | h162
                                        · rcases p158_3 (m.d 0 2) (by simp) with h163 | h163
                                          · linarith only [h0, h163, hlam]
                                          · linarith only [h126, h163, hlam]
                                        · linarith only [h162, h2, hlam]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        rcases p158_3 (m.d 0 1) (by simp) with h167 | h167
                                        · rcases p158_3 (m.d 0 2) (by simp) with h168 | h168
                                          · linarith only [h0, h168, hlam]
                                          · linarith only [h127, h168, hlam]
                                        · linarith only [h167, h3, hlam]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h0, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h4, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h148, h153, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p158_1, u3elo2]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p158_1, u3elo2]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h1, hlam, p158_1]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [hc02, hlam, hphi, ht23, p158_1, u3elo0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        rcases p158_3 (m.d 0 1) (by simp) with h180 | h180
                                        · rcases p158_3 (m.d 0 2) (by simp) with h181 | h181
                                          · linarith only [h181, h4, hlam]
                                          · linarith only [h126, h181, hlam]
                                        · linarith only [h180, h2, hlam]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        rcases p158_3 (m.d 0 1) (by simp) with h185 | h185
                                        · rcases p158_3 (m.d 0 2) (by simp) with h186 | h186
                                          · linarith only [h186, h4, hlam]
                                          · linarith only [h127, h186, hlam]
                                        · linarith only [h185, h3, hlam]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h2, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h126, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h128, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h130, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h3, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h127, hlam, p158_1]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h129, hlam, p158_0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [h148, h153, h2, hc34, hlam, hphi, ht45, p158_1, u5elo0]
                                      · have p158_0 := h158c.1
                                        have p158_1 := h158c.2.1
                                        have p158_2 := h158c.2.2.1
                                        have p158_3 := h158c.2.2.2
                                        linarith only [hlam, p158_0]
                                · linarith only [h153, h4, hc02, hlam, hphi, ht23, u3elo3]
                            · linarith only [h0, h128, h130, h148, h150, h4, hc13, hc24, hlam, hphi, ht45, u3elo2, u5elo4]
                          · linarith only [h148, h149, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h126, h148, h4, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h126, h129, h4, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h126, h128, h4, hlam]
              · linarith only [h126, h127, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
              · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h210 | h210
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
                      · linarith only [h0, h211, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                        · linarith only [h0, h126, h213, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                                    · linarith only [h1, h216, h220, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h2, h217, h220, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h126, h216, h217, h219, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h215, h218, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h208, h210, h213, h215, h217, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h208, h216, h4, hc13, hlam, hphi, u3elo2]
                          · linarith only [h126, h207, h215, hc12, hlam, hphi, u2elo3]
                    · linarith only [h126, h207, h210, hc25, hlam, hphi, u5elo4]
                  · linarith only [h208, h209, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h230 | h230
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h231 | h231
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                      · linarith only [h0, h208, h232, h4, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                        · linarith only [h126, h234, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h236 | h236
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                            · linarith only [h1, h208, h237, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                                · linarith only [h0, h208, h236, h240, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h0, h236, h240, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h208, h231, h237, h239, hc13, hlam, hphi, u3elo3]
                          · linarith only [h207, h236, h4, hc12, hlam, hphi, u2elo2]
                    · linarith only [h126, h207, h231, hc25, hlam, hphi, u5elo4]
                  · linarith only [h207, h230, h4, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h247 | h247
                · rcases m.htr 0 3 5 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h250 | h250
                      · linarith only [h0, h207, h250, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                        · linarith only [h0, h207, h252, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h0, h207, h254, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h257 | h257
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                                    · linarith only [h1, h256, h260, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h2, h257, h260, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h256, h257, h259, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h258, h4, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h247, h249, h252, h257, h4, hc12, hlam, hphi, ht23, u3elo2]
                            · linarith only [h247, h256, h4, hc13, hlam, hphi, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h267 | h267
                      · linarith only [h0, h207, h267, h4, hc03, hlam, hphi, ht34, ht45, u5elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                        · linarith only [h0, h126, h249, h269, hc24, hlam, hphi, ht45, u5elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                          · linarith only [h0, h126, h249, h271, hc25, hlam, hphi, u5elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                              · linarith only [h126, h2, h249, h274, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                                  · linarith only [h0, h126, h249, h276, h277, hc12, hlam, hphi, u2elo2]
                                  · linarith only [h0, h126, h277, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h1, h273, h276, hc23, hlam, hphi, u3elo0]
                            · linarith only [h247, h273, h4, hc13, hlam, hphi, u3elo2]
                  · linarith only [h247, h248, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h283 | h283
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                      · linarith only [h0, h285, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                        · linarith only [h0, h126, h287, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                          · linarith only [h0, h207, h289, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                            · linarith only [h247, h291, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                                · linarith only [h247, h294, hc03, hlam, hphi, u3elo2]
                                · linarith only [h0, h294, h4, hc12, hlam, hphi, ht23, u3elo3]
                              · linarith only [h247, h283, h284, h287, h293, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h247, h283, h284, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
                      · linarith only [h0, h300, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                        · linarith only [h0, h207, h302, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                          · linarith only [h0, h283, h304, h4, hc25, hlam, hphi, u5elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                            · linarith only [h1, h247, h306, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                                · linarith only [h247, h309, h4, hc02, hlam, hphi, u2elo2]
                                · linarith only [h0, h309, h4, hc12, hlam, hphi, ht23, u3elo3]
                              · linarith only [h247, h299, h302, h308, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                      · linarith only [h0, h313, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
                        · linarith only [h0, h126, h315, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                          · linarith only [h0, h207, h247, h299, h317, h4, hc05, hlam, hphi, u5elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                            · linarith only [h1, h247, h299, h319, hc34, hlam, hphi, ht45, u5elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                              · linarith only [h2, h247, h299, h321, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                                · linarith only [h0, h247, h323, h4, hc12, hlam, hphi, u2elo2]
                                · linarith only [h0, h323, h4, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h327 | h327
        · rcases m.htr 0 2 3 (by decide) (by decide) with h328 | h328
          · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
            · linarith only [h0, h2, h329, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h331 | h331
              · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
                · linarith only [h1, h2, h332, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                      · linarith only [h0, h2, h332, h336, hc23, hlam, hphi, u3elo3]
                      · linarith only [h328, h329, h336, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h335, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                      · linarith only [h0, h2, h332, h341, hc23, hlam, hphi, u3elo3]
                      · linarith only [h328, h329, h341, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h340, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h328, h331, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h346 | h346
            · linarith only [h0, h2, h328, h346, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h348 | h348
              · rcases m.htr 0 3 4 (by decide) (by decide) with h349 | h349
                · linarith only [h1, h2, h349, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                      · linarith only [h0, h328, h349, h353, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h355 | h355
                        · linarith only [h1, h2, h346, h353, h355, hlam]
                        · linarith only [h1, h2, h353, h355, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h352, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h328, h348, h351, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h360 | h360
                · linarith only [h1, h2, h360, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h362 | h362
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h363 | h363
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                      · linarith only [h0, h328, h364, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                        · linarith only [h0, h346, h366, hlam]
                        · linarith only [h0, h2, h366, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h363, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                      · linarith only [h0, h328, h371, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                        · linarith only [h0, h348, h373, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h1, h2, h371, h373, hc12, hlam, hphi, u2elo3]
                    · linarith only [h0, h2, h370, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h0, h327, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h379 | h379
    · rcases m.htr 0 1 4 (by decide) (by decide) with h380 | h380
      · rcases m.htr 0 1 5 (by decide) (by decide) with h381 | h381
        · rcases m.htr 0 2 3 (by decide) (by decide) with h382 | h382
          · rcases m.htr 0 2 4 (by decide) (by decide) with h383 | h383
            · rcases m.htr 0 2 5 (by decide) (by decide) with h384 | h384
              · rcases m.htr 0 3 4 (by decide) (by decide) with h385 | h385
                · rcases m.htr 0 3 5 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                            · linarith only [h0, h379, h391, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h385, h388, h391, hc23, hlam, hphi, u3elo0]
                          · linarith only [h0, h390, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h389, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h388, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h398 | h398
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
                            · linarith only [h0, h379, h400, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h0, h379, h385, h397, h400, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h399, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h379, h383, h397, h398, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h379, h397, hc13, hlam, hphi, u3elo2]
                  · linarith only [h385, h386, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                            · linarith only [h0, h379, h385, h407, h412, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h414 | h414
                              · linarith only [h0, h380, h414, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h0, h380, h408, h412, h414, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h0, h411, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h410, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h379, h409, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                    · linarith only [h385, h407, h408, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h421 | h421
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h424 | h424
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
                            · linarith only [h379, h385, h425, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h427 | h427
                              · linarith only [h0, h380, h427, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h0, h380, h421, h423, h427, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h0, h424, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h379, h422, h423, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h379, h422, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
                            · linarith only [h0, h379, h436, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h438 | h438
                              · linarith only [h0, h380, h385, h421, h438, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h440 | h440
                                · linarith only [h379, h385, h433, h440, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h442 | h442
                                  · linarith only [h0, h380, h421, h434, h442, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
                                    · linarith only [h379, h385, h421, h433, h444, hc23, hlam, hphi, u3elo3]
                                    · linarith only [h379, h385, h433, h444, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h435, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h0, h379, h433, h434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h379, h433, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h0, h379, h384, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h0, h380, h383, hlam]
          · linarith only [h0, h379, h382, hc13, hlam, hphi, u3elo2]
        · linarith only [h379, h381, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h454 | h454
        · rcases m.htr 0 2 3 (by decide) (by decide) with h455 | h455
          · rcases m.htr 0 2 4 (by decide) (by decide) with h456 | h456
            · rcases m.htr 0 2 5 (by decide) (by decide) with h457 | h457
              · rcases m.htr 0 3 4 (by decide) (by decide) with h458 | h458
                · linarith only [h379, h380, h458, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h464 | h464
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h465 | h465
                            · linarith only [h379, h458, h465, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h379, h380, h462, h465, hc23, hlam, hphi, u3elo3]
                          · linarith only [h379, h380, h462, h463, h464, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h456, h463, hlam]
                      · linarith only [h0, h379, h462, hc13, hlam, hphi, u3elo2]
                    · linarith only [h379, h380, h461, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h472 | h472
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h475 | h475
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
                            · linarith only [h0, h379, h476, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h379, h380, h476, hc13, hlam, hphi, u3elo3]
                          · linarith only [h379, h380, h473, h474, h475, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · linarith only [h0, h456, h474, hlam]
                      · linarith only [h0, h379, h473, hc13, hlam, hphi, u3elo2]
                    · linarith only [h379, h380, h472, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h379, h380, h456, h457, hc13, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h484 | h484
              · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
                · linarith only [h0, h379, h456, h485, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                        · linarith only [h0, h456, h490, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h379, h489, h490, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h379, h489, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                    · linarith only [h379, h380, h488, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h497 | h497
                        · linarith only [h456, h497, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h379, h496, h497, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h0, h379, h496, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                    · linarith only [h379, h380, h495, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h455, h484, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h379, h455, hc13, hlam, hphi, u3elo2]
        · linarith only [h379, h454, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h505 | h505
      · rcases m.htr 0 1 5 (by decide) (by decide) with h506 | h506
        · rcases m.htr 0 2 3 (by decide) (by decide) with h507 | h507
          · rcases m.htr 0 2 4 (by decide) (by decide) with h508 | h508
            · rcases m.htr 0 2 5 (by decide) (by decide) with h509 | h509
              · rcases m.htr 0 3 4 (by decide) (by decide) with h510 | h510
                · rcases m.htr 0 3 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h514 | h514
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
                              · linarith only [h379, h505, h517, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h379, h505, h512, h514, h517, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h379, h516, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h0, h505, h514, h515, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h379, h513, h514, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h507, h513, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
                              · linarith only [h379, h505, h528, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h531 | h531
                                  · linarith only [h0, h508, h512, h531, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h533 | h533
                                    · linarith only [h505, h512, h525, h530, h533, hlam]
                                    · rcases h0bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h0, hlam, p535_1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h379, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h379, h505, h525, h530, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p535_1, u3elo1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h379, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p535_1, u3elo1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p535_1, u2elo1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h0, h379, h505, h525, h530, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p535_1, u2elo1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        rcases p535_3 (m.d 0 1) (by simp) with h544 | h544
                                        · linarith only [h0, h544, hlam]
                                        · linarith only [h505, h544, hlam]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        rcases p535_3 (m.d 0 1) (by simp) with h547 | h547
                                        · linarith only [h0, h547, hlam]
                                        · linarith only [h506, h547, hlam]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h506, h525, h528, h530, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1, u0elo2]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h507, hlam, p535_1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        rcases p535_3 (m.d 0 1) (by simp) with h553 | h553
                                        · linarith only [h379, h553, hlam]
                                        · linarith only [h505, h553, hlam]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        rcases p535_3 (m.d 0 1) (by simp) with h556 | h556
                                        · linarith only [h379, h556, hlam]
                                        · linarith only [h506, h556, hlam]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h505, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h508, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h510, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h512, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h506, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h509, hlam, p535_1]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h511, hlam, p535_0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [h505, h525, h530, hc34, hlam, hphi, ht45, p535_1, u5elo0]
                                      · have p535_0 := h535c.1
                                        have p535_1 := h535c.2.1
                                        have p535_2 := h535c.2.2.1
                                        have p535_3 := h535c.2.2.2
                                        linarith only [hlam, p535_0]
                                · linarith only [h379, h510, h530, hc23, hlam, hphi, u3elo1]
                            · linarith only [h379, h506, h510, h527, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h0, h505, h525, h526, hc24, hlam, hphi, ht45, u5elo2]
                        · linarith only [h379, h505, h508, h512, h524, h525, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h505, h524, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h510, h511, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h379, h505, h510, hlam]
              · linarith only [h507, h509, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h379, h505, h507, h508, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h578 | h578
            · rcases m.htr 0 2 5 (by decide) (by decide) with h579 | h579
              · rcases m.htr 0 3 4 (by decide) (by decide) with h580 | h580
                · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h582 | h582
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
                      · linarith only [h507, h583, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h505, h583, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
                      · linarith only [h0, h505, h507, h586, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h505, h586, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h0, h505, h507, h581, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h505, h507, h580, hlam]
              · linarith only [h0, h505, h579, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h505, h578, hlam]
        · linarith only [h505, h506, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
        · rcases m.htr 0 2 3 (by decide) (by decide) with h595 | h595
          · rcases m.htr 0 2 4 (by decide) (by decide) with h596 | h596
            · rcases m.htr 0 2 5 (by decide) (by decide) with h597 | h597
              · rcases m.htr 0 3 4 (by decide) (by decide) with h598 | h598
                · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h600 | h600
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h605 | h605
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h606 | h606
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h607 | h607
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h608 | h608
                                    · linarith only [h595, h606, h608, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h505, h594, h603, h604, h607, h608, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                  · linarith only [h505, h594, h604, h605, h607, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h379, h598, h606, hc23, hlam, hphi, u3elo1]
                              · linarith only [h505, h605, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h379, h595, h598, h604, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h595, h598, h603, hc34, hlam, hphi, ht45, u5elo2]
                        · linarith only [h379, h594, h601, h602, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h595, h601, hc12, hlam, hphi, u2elo0]
                    · linarith only [h505, h594, h600, hc15, hlam, hphi, u5elo4]
                  · linarith only [h598, h599, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                            · linarith only [h379, h594, h598, h622, h624, h625, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h379, h594, h624, h625, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h0, h624, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h379, h594, h596, h622, h623, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h594, h622, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h598, h620, h621, hc35, hlam, hphi, u5elo4]
                  · linarith only [h379, h594, h620, hc15, hlam, hphi, u5elo3]
              · linarith only [h595, h597, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h634 | h634
              · rcases m.htr 0 3 4 (by decide) (by decide) with h635 | h635
                · linarith only [h595, h596, h635, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h640 | h640
                        · linarith only [h595, h596, h640, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h594, h640, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                      · linarith only [h0, h594, h595, h639, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h595, h596, h638, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h379, h594, h637, hc15, hlam, hphi, u5elo3]
              · linarith only [h595, h634, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h647 | h647
            · rcases m.htr 0 2 5 (by decide) (by decide) with h648 | h648
              · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
                · rcases m.htr 0 3 5 (by decide) (by decide) with h650 | h650
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h651 | h651
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                      · linarith only [h505, h594, h595, h647, h652, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h594, h652, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h505, h594, h651, hc15, hlam, hphi, u5elo4]
                  · linarith only [h505, h594, h595, h647, h650, hc15, hlam, hphi, u5elo3]
                · linarith only [h595, h647, h649, hlam]
              · linarith only [h505, h594, h647, h648, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h659 | h659
              · rcases m.htr 0 3 4 (by decide) (by decide) with h660 | h660
                · rcases m.htr 0 3 5 (by decide) (by decide) with h661 | h661
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h662 | h662
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                      · linarith only [h595, h663, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h594, h663, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h0, h594, h647, h662, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h594, h647, h660, h661, hc15, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h668 | h668
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h669 | h669
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                      · linarith only [h0, h594, h595, h670, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h594, h670, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h660, h668, h669, hc35, hlam, hphi, u5elo4]
                  · linarith only [h0, h594, h595, h668, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h594, h659, hc15, hlam, hphi, u5elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h676 | h676
          · rcases m.htr 0 2 4 (by decide) (by decide) with h677 | h677
            · rcases m.htr 0 2 5 (by decide) (by decide) with h678 | h678
              · rcases m.htr 0 3 4 (by decide) (by decide) with h679 | h679
                · rcases m.htr 0 3 5 (by decide) (by decide) with h680 | h680
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h681 | h681
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h682 | h682
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h683 | h683
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h684 | h684
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h685 | h685
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h686 | h686
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h687 | h687
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h688 | h688
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h689 | h689
                                    · linarith only [h676, h687, h689, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h0, h677, h688, h689, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h692 | h692
                                    · linarith only [h687, h688, h692, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                    · rcases h0bigk with h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h0, hlam, p694_1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h379, hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h505, hlam, p694_1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h594, hlam, p694_1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p694_1, u2elo0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h0, h379, hc01, hlam, hphi, ht12, p694_1, u2elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h0, h505, hc01, hlam, hphi, ht12, p694_1, u2elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h0, h594, hc01, hlam, hphi, ht12, p694_1, u2elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p694_1, u3elo0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h676, hlam, p694_1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h379, h505, hc01, hlam, hphi, ht12, ht23, p694_1, u3elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h379, h594, hc01, hlam, hphi, ht12, ht23, p694_1, u3elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h505, h685, hc01, hlam, hphi, ht12, ht23, p694_1, u3elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h677, hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h679, hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h505, h594, h685, hc01, hlam, hphi, ht12, ht23, p694_1, u3elo1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p694_1, u5elo0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h678, hlam, p694_1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h680, hlam, p694_0]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [h681, hlam, p694_1]
                                      · have p694_0 := h694c.1
                                        have p694_1 := h694c.2.1
                                        have p694_2 := h694c.2.2.1
                                        have p694_3 := h694c.2.2.2
                                        linarith only [hlam, p694_0]
                                · linarith only [h379, h679, h687, hc23, hlam, hphi, u3elo1]
                              · linarith only [h505, h681, h686, hlam]
                            · linarith only [h379, h679, h685, hlam]
                          · linarith only [h0, h678, h684, hlam]
                        · linarith only [h0, h683, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h682, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h730 | h730
                              · linarith only [h505, h681, h727, h730, hc01, hlam, hphi, ht12, u2elo1]
                              · linarith only [h505, h730, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h379, h729, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h678, h728, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h727, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h726, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h679, h680, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h738 | h738
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h742 | h742
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h743 | h743
                            · linarith only [h679, h743, hc03, hlam, hphi, u3elo1]
                            · linarith only [h379, h743, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h678, h742, hc12, hlam, hphi, u2elo0]
                        · linarith only [h0, h741, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h740, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h679, h738, h739, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h754 | h754
                            · linarith only [h679, h754, hc03, hlam, hphi, u3elo1]
                            · linarith only [h379, h754, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h0, h678, h753, hlam]
                        · linarith only [h0, h677, h752, hlam]
                      · linarith only [h0, h676, h751, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                            · linarith only [h379, h679, h763, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · linarith only [h379, h763, hc01, hlam, hphi, ht12, ht23, u3elo3]
                          · linarith only [h0, h678, h762, hlam]
                        · linarith only [h0, h677, h761, hlam]
                      · linarith only [h0, h676, h760, hlam]
              · linarith only [h676, h678, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h770 | h770
              · rcases m.htr 0 3 4 (by decide) (by decide) with h771 | h771
                · linarith only [h676, h677, h771, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h773 | h773
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h774 | h774
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h776 | h776
                        · linarith only [h676, h677, h776, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h776, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h676, h775, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h676, h677, h774, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h783 | h783
                        · linarith only [h676, h677, h783, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h783, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h676, h782, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h676, h677, h781, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h676, h770, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h789 | h789
            · rcases m.htr 0 2 5 (by decide) (by decide) with h790 | h790
              · rcases m.htr 0 3 4 (by decide) (by decide) with h791 | h791
                · rcases m.htr 0 3 5 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h793 | h793
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
                      · linarith only [h676, h789, h794, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h794, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h797 | h797
                      · linarith only [h676, h789, h797, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h797, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h676, h789, h792, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h676, h789, h791, hlam]
              · linarith only [h789, h790, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h803 | h803
              · rcases m.htr 0 3 4 (by decide) (by decide) with h804 | h804
                · rcases m.htr 0 3 5 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h806 | h806
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
                      · linarith only [h676, h807, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h807, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h789, h803, h806, hc25, hlam, hphi, u5elo4]
                  · linarith only [h804, h805, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h812 | h812
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h813 | h813
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                      · linarith only [h676, h803, h814, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h814, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h676, h803, h804, h813, hc25, hlam, hphi, u5elo4]
                  · linarith only [h676, h803, h812, hc25, hlam, hphi, u5elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h819 | h819
                · rcases m.htr 0 3 5 (by decide) (by decide) with h820 | h820
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
                      · linarith only [h676, h822, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h822, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                      · linarith only [h0, h676, h825, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h825, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h819, h820, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h829 | h829
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h830 | h830
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
                      · linarith only [h0, h676, h831, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h831, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h819, h829, h830, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
                      · linarith only [h0, h676, h836, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h836, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
                      · linarith only [h0, h676, h839, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h839, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
