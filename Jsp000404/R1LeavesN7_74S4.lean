import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_I_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
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
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h0, h12, h14, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h13, hc14, hlam, hphi, ht45, u5elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                              · linarith only [h0, h19, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                                · linarith only [h0, h12, h21, h4, h7, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h21, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h18, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h11, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h10, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                      · linarith only [h0, h27, h4, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                        · linarith only [h0, h29, h4, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h29, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h8, hc04, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                          · linarith only [h1, h37, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                              · linarith only [h34, h40, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h0, h34, h42, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h42, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h37, h39, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h36, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h34, h35, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                      · linarith only [h0, h34, h4, h48, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                        · linarith only [h0, h34, h4, h50, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h50, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h33, h7, hc03, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
              · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
                · linarith only [h4, h5, h56, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                      · linarith only [h0, h5, h60, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                          · linarith only [h1, h56, h63, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                              · linarith only [h0, h5, h56, h59, h66, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                                · linarith only [h0, h59, h68, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h68, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h65, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h59, h62, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h4, h5, h59, hc12, hc24, hlam, hphi]
                  · linarith only [h5, h58, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h4, h55, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h76 | h76
            · rcases m.htr 0 2 5 (by decide) (by decide) with h77 | h77
              · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
                · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                    · linarith only [h4, h76, h80, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                                  · linarith only [h0, h82, h88, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h88, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h4, h87, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h2, h4, h76, h78, h85, h86, hc03, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h85, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1, h78, h80, h82, h84, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h82, h83, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h4, h76, h82, hc12, hc23, hlam, hphi]
                  · linarith only [h79, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h4, h76, h78, hlam]
              · linarith only [h77, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
                · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
                      · linarith only [h0, h105, h76, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                                    · linarith only [h1, h108, h113, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                    · linarith only [h113, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h107, h109, h111, h112, h76, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                                · linarith only [h110, h111, h76, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h101, h110, h4, hlam]
                            · linarith only [h109, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1, h101, h103, h107, h108, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h107, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h102, h76, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h124, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h0, h126, h76, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                          · linarith only [h1, h101, h129, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                    · rcases h2bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h101, h128, h132, h133, h135, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h4, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h76, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h101, h132, h133, h135, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, hlam, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h124, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h126, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h133, h135, hc45, hlam, hphi, ht01, ht0b, ht5b, p136_1, u1elo0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        rcases p136_3 (m.d 0 2) (by simp) with h147 | h147
                                        · linarith only [h147, hlam, p136_0]
                                        · rcases p136_3 (m.d 1 2) (by simp) with h149 | h149
                                          · linarith only [h124, h149, hlam]
                                          · rcases p136_3 (m.d 2 3) (by simp) with h151 | h151
                                            · rcases p136_3 (m.d 2 4) (by simp) with h152 | h152
                                              · linarith only [h132, h152, hlam]
                                              · linarith only [h152, h76, hlam]
                                            · linarith only [h151, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        rcases p136_3 (m.d 0 2) (by simp) with h156 | h156
                                        · linarith only [h156, h4, hlam]
                                        · linarith only [h0, h156, hlam]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h101, h132, h4, hc02, hc23, hlam, hphi, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h0, h101, h128, h132, h4, hlam, p136_2]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        rcases p136_3 (m.d 0 2) (by simp) with h162 | h162
                                        · linarith only [h162, hlam, p136_0]
                                        · rcases p136_3 (m.d 1 2) (by simp) with h164 | h164
                                          · linarith only [h126, h164, hlam]
                                          · rcases p136_3 (m.d 2 3) (by simp) with h166 | h166
                                            · rcases p136_3 (m.d 2 4) (by simp) with h167 | h167
                                              · rcases p136_3 (m.d 2 5) (by simp) with h168 | h168
                                                · linarith only [h134, h168, hlam]
                                                · rcases h4bigk with h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c | h170c
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h124, h128, h129, h133, h135, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p170_1, u1elo0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h76, hlam, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h101, hlam, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    rcases p170_3 (m.d 0 4) (by simp) with h175 | h175
                                                    · rcases p170_3 (m.d 1 4) (by simp) with h176 | h176
                                                      · linarith only [h176, h2, hlam]
                                                      · linarith only [h131, h176, hlam]
                                                    · linarith only [h175, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h2, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h126, hlam, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h129, hlam, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p170_1, u1elo0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    rcases p170_3 (m.d 0 4) (by simp) with h185 | h185
                                                    · linarith only [h185, h76, hlam]
                                                    · rcases p170_3 (m.d 1 4) (by simp) with h187 | h187
                                                      · linarith only [h126, h187, hlam]
                                                      · rcases p170_3 (m.d 2 4) (by simp) with h189 | h189
                                                        · rcases p170_3 (m.d 3 4) (by simp) with h190 | h190
                                                          · linarith only [h132, h190, hlam]
                                                          · linarith only [h101, h190, hlam]
                                                        · linarith only [h189, h76, hlam]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    rcases p170_3 (m.d 0 4) (by simp) with h194 | h194
                                                    · linarith only [h194, h76, hlam]
                                                    · linarith only [h194, h2, hlam]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h0, h101, h128, h132, h133, h135, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h0, h128, h133, h135, hlam, p136_1, p170_2]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h0, h101, h128, h132, h133, h135, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h126, h128, h132, h133, h135, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p170_1]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h132, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    rcases p170_3 (m.d 0 4) (by simp) with h204 | h204
                                                    · linarith only [h101, h204, hlam]
                                                    · linarith only [h123, h204, hlam]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h123, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h131, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h134, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [h135, hlam, p170_0]
                                                  · have p170_0 := h170c.1
                                                    have p170_1 := h170c.2.1
                                                    have p170_2 := h170c.2.2.1
                                                    have p170_3 := h170c.2.2.2
                                                    linarith only [hlam, p170_0]
                                              · linarith only [h167, hlam, p136_0]
                                            · linarith only [h166, h4, hlam]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        rcases p136_3 (m.d 0 2) (by simp) with h214 | h214
                                        · linarith only [h214, h76, hlam]
                                        · linarith only [h0, h214, hlam]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h132, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        rcases p136_3 (m.d 0 2) (by simp) with h219 | h219
                                        · linarith only [h219, h76, hlam]
                                        · linarith only [h100, h219, hlam]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h100, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h128, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h133, hlam, p136_0]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [h134, hlam, p136_1]
                                      · have p136_0 := h136c.1
                                        have p136_1 := h136c.2.1
                                        have p136_2 := h136c.2.2.1
                                        have p136_3 := h136c.2.2.2
                                        linarith only [hlam, p136_0]
                                    · linarith only [h135, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h134, hc24, hlam, hphi, ht45, u5elo4]
                                · linarith only [h133, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                                    · rcases h2bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h132, h4, hc12, hc34, hlam, hphi, ht23, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h4, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h76, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h132, h230, h232, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, hlam, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h124, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h126, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, h230, h232, hc45, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h132, hc02, hc34, hlam, hphi, ht23, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h132, hc12, hc34, hlam, hphi, ht23, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h132, hlam, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        rcases p233_3 (m.d 0 2) (by simp) with h248 | h248
                                        · linarith only [h248, h4, hlam]
                                        · linarith only [h100, h248, hlam]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        rcases p233_3 (m.d 0 2) (by simp) with h251 | h251
                                        · linarith only [h251, hlam, p233_0]
                                        · rcases p233_3 (m.d 1 2) (by simp) with h253 | h253
                                          · linarith only [h126, h253, hlam]
                                          · rcases p233_3 (m.d 2 3) (by simp) with h255 | h255
                                            · linarith only [h132, h255, hlam]
                                            · linarith only [h255, h4, hlam]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        rcases p233_3 (m.d 0 2) (by simp) with h258 | h258
                                        · linarith only [h258, h76, hlam]
                                        · linarith only [h0, h258, hlam]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, h128, h230, h232, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        rcases p233_3 (m.d 0 2) (by simp) with h263 | h263
                                        · linarith only [h263, h76, hlam]
                                        · linarith only [h100, h263, hlam]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h100, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h128, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h230, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h231, hlam, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                    · linarith only [h232, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h131, h231, h3, hc24, hlam, hphi, ht45, u5elo0]
                                · linarith only [h230, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h131, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h128, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h101, h123, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h100, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h279 | h279
        · rcases m.htr 0 2 3 (by decide) (by decide) with h280 | h280
          · rcases m.htr 0 2 4 (by decide) (by decide) with h281 | h281
            · linarith only [h0, h2, h281, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h283 | h283
              · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
                · linarith only [h1, h2, h284, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                    · linarith only [h0, h2, h287, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h0, h2, h280, h287, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h2, h286, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h280, h283, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
            · linarith only [h0, h2, h292, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h294 | h294
              · rcases m.htr 0 3 4 (by decide) (by decide) with h295 | h295
                · linarith only [h1, h2, h295, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
                    · linarith only [h0, h2, h280, h298, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h300 | h300
                      · linarith only [h1, h2, h292, h294, h298, h300, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                        · linarith only [h1, h2, h298, h302, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h280, h294, h302, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h297, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h294, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h279, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h308 | h308
      · rcases m.htr 0 1 5 (by decide) (by decide) with h309 | h309
        · rcases m.htr 0 2 3 (by decide) (by decide) with h310 | h310
          · linarith only [h0, h1, h310, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h312 | h312
            · rcases m.htr 0 2 5 (by decide) (by decide) with h313 | h313
              · rcases m.htr 0 3 4 (by decide) (by decide) with h314 | h314
                · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
                    · linarith only [h0, h1, h310, h316, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                      · linarith only [h0, h1, h318, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h312, h318, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h315, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h1, h308, h314, hlam]
              · linarith only [h313, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h324 | h324
              · rcases m.htr 0 3 4 (by decide) (by decide) with h325 | h325
                · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                    · linarith only [h0, h1, h327, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
                      · linarith only [h0, h1, h312, h324, h329, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                        · linarith only [h1, h308, h329, h331, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h312, h324, h331, hc12, hc24, hlam, hphi]
                  · linarith only [h312, h326, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h1, h308, h325, hlam]
              · linarith only [h324, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h309, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h338 | h338
        · rcases m.htr 0 2 3 (by decide) (by decide) with h339 | h339
          · linarith only [h0, h1, h339, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h341 | h341
            · linarith only [h0, h308, h341, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h343 | h343
              · rcases m.htr 0 3 4 (by decide) (by decide) with h344 | h344
                · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                    · linarith only [h0, h1, h339, h346, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                      · linarith only [h0, h1, h341, h343, h348, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
                        · linarith only [h0, h1, h350, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h350, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h308, h345, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
                    · linarith only [h0, h1, h339, h355, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h357 | h357
                      · linarith only [h0, h1, h341, h344, h357, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h0, h308, h359, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h359, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h1, h344, h354, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h343, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h338, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h365 | h365
    · rcases m.htr 0 1 4 (by decide) (by decide) with h366 | h366
      · rcases m.htr 0 1 5 (by decide) (by decide) with h367 | h367
        · rcases m.htr 0 2 3 (by decide) (by decide) with h368 | h368
          · rcases m.htr 0 2 4 (by decide) (by decide) with h369 | h369
            · rcases m.htr 0 2 5 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 3 4 (by decide) (by decide) with h371 | h371
                · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                          · linarith only [h0, h365, h376, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h0, h365, h371, h376, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h0, h375, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h366, h369, h374, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h368, h373, hlam]
                  · linarith only [h372, hc04, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                          · linarith only [h0, h365, h371, h387, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h389 | h389
                            · linarith only [h0, h366, h389, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h389, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h386, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h367, h369, h385, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h368, h384, hlam]
                  · linarith only [h383, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h370, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h366, h369, hlam]
          · linarith only [h0, h365, h368, hlam]
        · linarith only [h367, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h400 | h400
        · rcases m.htr 0 2 3 (by decide) (by decide) with h401 | h401
          · rcases m.htr 0 2 4 (by decide) (by decide) with h402 | h402
            · rcases m.htr 0 2 5 (by decide) (by decide) with h403 | h403
              · rcases m.htr 0 3 4 (by decide) (by decide) with h404 | h404
                · linarith only [h365, h366, h404, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h406 | h406
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                          · linarith only [h365, h366, h404, h408, h410, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                              · linarith only [h365, h366, h407, h410, h413, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h415 | h415
                                · linarith only [h365, h366, h407, h408, h415, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h415, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h365, h366, h412, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h366, h403, h408, h409, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                      · linarith only [h0, h402, h408, hlam]
                    · linarith only [h0, h401, h407, hlam]
                  · linarith only [h406, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h403, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
                · linarith only [h0, h365, h402, h425, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                      · linarith only [h0, h365, h402, h428, h429, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                          · linarith only [h365, h425, h432, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                              · linarith only [h0, h428, h429, h432, h435, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h365, h428, h429, h435, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h365, h428, h429, h434, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h365, h428, h431, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h0, h401, h428, hlam]
                  · linarith only [h427, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h424, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h365, h401, hlam]
        · linarith only [h365, h400, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h445 | h445
      · rcases m.htr 0 1 5 (by decide) (by decide) with h446 | h446
        · rcases m.htr 0 2 3 (by decide) (by decide) with h447 | h447
          · rcases m.htr 0 2 4 (by decide) (by decide) with h448 | h448
            · rcases m.htr 0 2 5 (by decide) (by decide) with h449 | h449
              · rcases m.htr 0 3 4 (by decide) (by decide) with h450 | h450
                · rcases m.htr 0 4 5 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h456 | h456
                            · linarith only [h365, h445, h452, h456, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h456, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h365, h446, h447, h450, h455, hc02, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h454, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h365, h445, h448, h452, h453, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h447, h452, hlam]
                  · linarith only [h451, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h365, h445, h450, hlam]
              · linarith only [h449, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h365, h445, h447, h448, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h467 | h467
            · rcases m.htr 0 2 5 (by decide) (by decide) with h468 | h468
              · rcases m.htr 0 3 4 (by decide) (by decide) with h469 | h469
                · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                    · linarith only [h447, h467, h471, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h473 | h473
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                            · linarith only [h0, h445, h476, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h476, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h445, h469, h471, h473, h475, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h445, h473, h474, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h0, h445, h467, h473, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h470, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h0, h445, h447, h469, hlam]
              · linarith only [h0, h468, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h445, h467, hlam]
        · linarith only [h445, h446, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h487 | h487
        · rcases m.htr 0 2 3 (by decide) (by decide) with h488 | h488
          · rcases m.htr 0 2 4 (by decide) (by decide) with h489 | h489
            · rcases m.htr 0 2 5 (by decide) (by decide) with h490 | h490
              · rcases m.htr 0 3 4 (by decide) (by decide) with h491 | h491
                · rcases m.htr 0 4 5 (by decide) (by decide) with h492 | h492
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h493 | h493
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h494 | h494
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h495 | h495
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h497 | h497
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h500 | h500
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h501 | h501
                                    · linarith only [h0, h488, h498, h501, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                    · linarith only [h501, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h445, h487, h497, h500, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                                · linarith only [h499, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h506 | h506
                                · linarith only [h365, h491, h493, h498, h506, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                · linarith only [h506, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h445, h497, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h365, h445, h487, h491, h495, h496, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h0, h495, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h365, h487, h489, h493, h494, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h488, h493, hlam]
                  · linarith only [h445, h487, h492, hc15, hlam, hphi, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h515 | h515
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h517 | h517
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h518 | h518
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
                          · linarith only [h365, h487, h491, h518, h519, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h522 | h522
                              · linarith only [h365, h487, h488, h518, h519, h522, hc03, hc25, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h525 | h525
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h526 | h526
                                    · rcases h2bigk with h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c | h527c
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, h522, h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        rcases p527_3 (m.d 0 2) (by simp) with h532 | h532
                                        · rcases p527_3 (m.d 1 2) (by simp) with h533 | h533
                                          · rcases p527_3 (m.d 2 3) (by simp) with h534 | h534
                                            · linarith only [h488, h534, hlam]
                                            · linarith only [h524, h534, hlam]
                                          · linarith only [h518, h533, hlam]
                                        · linarith only [h532, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, h487, h518, h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h522, h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        rcases p527_3 (m.d 0 2) (by simp) with h543 | h543
                                        · linarith only [h0, h543, hlam]
                                        · linarith only [h490, h543, hlam]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h488, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h516, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h522, hlam, p527_1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, h489, h522, h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h489, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h517, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, h489, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h0, h489, h524, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p527_1, u1elo1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h490, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h518, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h524, hlam, p527_0]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [h525, hlam, p527_1]
                                      · have p527_0 := h527c.1
                                        have p527_1 := h527c.2.1
                                        have p527_2 := h527c.2.2.1
                                        have p527_3 := h527c.2.2.2
                                        linarith only [hlam, p527_0]
                                    · linarith only [h365, h519, h526, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h365, h487, h521, h525, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                · linarith only [h524, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h521, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h518, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h365, h487, h489, h516, h517, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h488, h516, hlam]
                  · linarith only [h515, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h488, h490, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h570 | h570
              · rcases m.htr 0 3 4 (by decide) (by decide) with h571 | h571
                · linarith only [h488, h489, h571, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h575 | h575
                      · linarith only [h488, h489, h575, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h578 | h578
                          · linarith only [h365, h487, h571, h577, h578, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                              · linarith only [h0, h488, h575, h578, h581, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h584 | h584
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h585 | h585
                                    · rcases h2bigk with h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h0, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h0, h575, h581, h583, h585, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h489, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        rcases p586_3 (m.d 0 2) (by simp) with h591 | h591
                                        · rcases p586_3 (m.d 1 2) (by simp) with h592 | h592
                                          · rcases p586_3 (m.d 2 3) (by simp) with h593 | h593
                                            · linarith only [h488, h593, hlam]
                                            · linarith only [h583, h593, hlam]
                                          · linarith only [h577, h592, hlam]
                                        · linarith only [h591, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h575, h581, hc02, hc34, hlam, hphi, ht23, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h575, h581, h583, h585, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h575, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        rcases p586_3 (m.d 0 2) (by simp) with h602 | h602
                                        · linarith only [h0, h602, hlam]
                                        · linarith only [h570, h602, hlam]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h488, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h574, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h581, hlam, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h0, h488, h575, h581, h583, h585, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h488, h581, hc23, hc34, hlam, hphi, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h0, h487, h577, h581, h583, h585, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        rcases p586_3 (m.d 0 2) (by simp) with h612 | h612
                                        · linarith only [h489, h612, hlam]
                                        · linarith only [h488, h612, hlam]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h365, h487, h574, h575, h577, hlam, p586_2]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h570, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h577, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h583, hlam, p586_0]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [h584, hlam, p586_1]
                                      · have p586_0 := h586c.1
                                        have p586_1 := h586c.2.1
                                        have p586_2 := h586c.2.2.1
                                        have p586_3 := h586c.2.2.2
                                        linarith only [hlam, p586_0]
                                    · linarith only [h585, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h365, h487, h574, h575, h580, h584, hlam]
                                · linarith only [h365, h487, h574, h575, h581, h583, hc15, hc23, hc34, hlam, hphi, u5elo3]
                            · linarith only [h365, h487, h574, h575, h577, h580, hc25, hlam, hphi, u5elo4]
                        · linarith only [h365, h487, h574, h577, hc15, hlam, hphi, u5elo2]
                    · linarith only [h0, h487, h488, h574, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h489, h573, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h488, h570, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h630 | h630
            · rcases m.htr 0 2 5 (by decide) (by decide) with h631 | h631
              · rcases m.htr 0 3 4 (by decide) (by decide) with h632 | h632
                · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
                    · linarith only [h445, h487, h488, h630, h634, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h639 | h639
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h643 | h643
                                    · rcases h2bigk with h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c | h644c
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h0, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h488, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h0, h640, h643, hc45, hlam, hphi, ht01, ht0b, ht5b, p644_1, u1elo1]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        rcases p644_3 (m.d 0 2) (by simp) with h649 | h649
                                        · rcases p644_3 (m.d 1 2) (by simp) with h650 | h650
                                          · rcases p644_3 (m.d 2 3) (by simp) with h651 | h651
                                            · rcases p644_3 (m.d 2 4) (by simp) with h652 | h652
                                              · linarith only [h630, h652, hlam]
                                              · linarith only [h642, h652, hlam]
                                            · linarith only [h641, h651, hlam]
                                          · linarith only [h637, h650, hlam]
                                        · linarith only [h649, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h0, h487, h634, h637, h641, h643, hc45, hlam, hphi, ht01, ht0b, ht5b, p644_1, u1elo2]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h634, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h634, h640, h643, hc45, hlam, hphi, ht01, ht0b, ht5b, p644_1, u1elo2]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        rcases p644_3 (m.d 0 2) (by simp) with h662 | h662
                                        · linarith only [h0, h662, hlam]
                                        · linarith only [h631, h662, hlam]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h630, h640, h643, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p644_1]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h0, h487, h637, h641, h643, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p644_1]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        rcases p644_3 (m.d 0 2) (by simp) with h668 | h668
                                        · linarith only [h488, h668, hlam]
                                        · linarith only [h630, h668, hlam]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h445, h487, h634, h636, h637, hlam, p644_2]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h630, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h636, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h640, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h0, h630, h641, h643, hc45, hlam, hphi, ht01, ht0b, ht5b, p644_1, u1elo1]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h631, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h637, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h641, hlam, p644_0]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [h642, hlam, p644_1]
                                      · have p644_0 := h644c.1
                                        have p644_1 := h644c.2.1
                                        have p644_2 := h644c.2.2.1
                                        have p644_3 := h644c.2.2.2
                                        linarith only [hlam, p644_0]
                                    · linarith only [h643, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h445, h487, h639, h642, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                                · linarith only [h445, h634, h636, h641, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h445, h487, h634, h636, h639, h640, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h445, h487, h637, h639, hc25, hlam, hphi, u5elo4]
                          · linarith only [h365, h445, h487, h632, h636, h637, h638, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h445, h487, h636, h637, hc15, hlam, hphi, u5elo2]
                      · linarith only [h0, h630, h636, hlam]
                  · linarith only [h633, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h488, h630, h632, hlam]
              · linarith only [h631, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h693 | h693
              · rcases m.htr 0 3 4 (by decide) (by decide) with h694 | h694
                · rcases m.htr 0 4 5 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h696 | h696
                    · linarith only [h0, h487, h488, h696, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h698 | h698
                      · linarith only [h0, h487, h630, h696, h698, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h700 | h700
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h702 | h702
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h704 | h704
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h705 | h705
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h706 | h706
                                    · rcases h2bigk with h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c | h707c
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h488, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h630, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        rcases p707_3 (m.d 0 2) (by simp) with h712 | h712
                                        · rcases p707_3 (m.d 1 2) (by simp) with h713 | h713
                                          · rcases p707_3 (m.d 2 3) (by simp) with h714 | h714
                                            · rcases p707_3 (m.d 2 4) (by simp) with h715 | h715
                                              · rcases p707_3 (m.d 2 5) (by simp) with h716 | h716
                                                · linarith only [h716, hlam, p707_0]
                                                · rcases h4bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h445, hlam, p718_1]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h630, hlam, p718_1]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h365, h694, h706, hc45, hlam, hphi, ht01, ht0b, ht5b, p718_1, u1elo2]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    rcases p718_3 (m.d 0 4) (by simp) with h723 | h723
                                                    · rcases p718_3 (m.d 1 4) (by simp) with h724 | h724
                                                      · rcases p718_3 (m.d 2 4) (by simp) with h725 | h725
                                                        · rcases p718_3 (m.d 3 4) (by simp) with h726 | h726
                                                          · linarith only [h694, h726, hlam]
                                                          · linarith only [h706, h726, hlam]
                                                        · linarith only [h705, h725, hlam]
                                                      · linarith only [h702, h724, hlam]
                                                    · linarith only [h723, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h445, h487, h700, h701, h704, h706, hc45, hlam, hphi, ht01, ht0b, ht5b, p718_1, u1elo2]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h698, hlam, p718_1]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h701, h706, hc45, hlam, hphi, ht01, ht0b, ht5b, p718_1, u1elo2]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    rcases p718_3 (m.d 0 4) (by simp) with h736 | h736
                                                    · linarith only [h445, h736, hlam]
                                                    · linarith only [h695, h736, hlam]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h630, h704, h706, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1, p718_1]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h0, h487, h698, h700, h704, h706, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p718_1]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    rcases p718_3 (m.d 0 4) (by simp) with h742 | h742
                                                    · linarith only [h630, h742, hlam]
                                                    · linarith only [h694, h742, hlam]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h630, h704, h706, hlam, p707_1, p718_2]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h694, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h701, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h703, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h365, h694, hc45, hlam, hphi, ht01, ht0b, ht5b, p718_1, u1elo2]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h695, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h702, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h705, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [h706, hlam, p718_0]
                                                  · have p718_0 := h718c.1
                                                    have p718_1 := h718c.2.1
                                                    have p718_2 := h718c.2.2.1
                                                    have p718_3 := h718c.2.2.2
                                                    linarith only [hlam, p718_0]
                                              · linarith only [h705, h715, hlam]
                                            · linarith only [h704, h714, hlam]
                                          · linarith only [h700, h713, hlam]
                                        · linarith only [h712, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, h487, h698, h700, h704, h706, hc45, hlam, hphi, ht01, ht0b, ht5b, p707_1, u1elo3]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h696, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h698, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        rcases p707_3 (m.d 0 2) (by simp) with h764 | h764
                                        · linarith only [h0, h764, hlam]
                                        · linarith only [h693, h764, hlam]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        rcases p707_3 (m.d 0 2) (by simp) with h767 | h767
                                        · linarith only [h767, hlam, p707_0]
                                        · rcases p707_3 (m.d 1 2) (by simp) with h769 | h769
                                          · linarith only [h696, h769, hlam]
                                          · linarith only [h0, h769, hlam]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, h487, h700, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, h487, h698, h700, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, h487, h696, h700, hlam, p707_2]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        rcases p707_3 (m.d 0 2) (by simp) with h776 | h776
                                        · linarith only [h776, hlam, p707_0]
                                        · rcases p707_3 (m.d 1 2) (by simp) with h778 | h778
                                          · linarith only [h698, h778, hlam]
                                          · linarith only [h0, h778, hlam]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, h487, h700, h703, h704, h706, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p707_1]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h703, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h0, h487, h698, h700, hlam, p707_2]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h693, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h700, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h704, hlam, p707_0]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [h705, hlam, p707_1]
                                      · have p707_0 := h707c.1
                                        have p707_1 := h707c.2.1
                                        have p707_2 := h707c.2.2.1
                                        have p707_3 := h707c.2.2.2
                                        linarith only [hlam, p707_0]
                                    · linarith only [h706, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h487, h698, h702, h705, hlam]
                                · linarith only [h704, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h0, h696, h703, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h702, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h365, h445, h487, h694, h700, h701, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h0, h487, h700, hc15, hlam, hphi, u5elo2]
                  · linarith only [h630, h695, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h799 | h799
                    · linarith only [h0, h487, h488, h799, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h801 | h801
                      · linarith only [h0, h487, h630, h799, h801, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h803 | h803
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h804 | h804
                          · linarith only [h365, h487, h694, h803, h804, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h806 | h806
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h807 | h807
                              · linarith only [h0, h487, h799, h803, h804, h807, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h487, h799, h803, h807, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h806, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h487, h803, hc15, hlam, hphi, u5elo2]
                  · linarith only [h488, h694, h798, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h487, h693, hc15, hlam, hphi, u5elo2]
        · linarith only [h487, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
