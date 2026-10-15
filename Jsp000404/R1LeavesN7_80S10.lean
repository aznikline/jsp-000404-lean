import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LR_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h3, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h0, h10, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h0, h14, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h0, h17, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
          · linarith only [h21, h3, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
            · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                · linarith only [h25, h3, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                  · linarith only [h1, h21, h25, h27, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                              · linarith only [h1, h29, h34, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1, h29, h30, h34, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h21, h29, h30, h33, hlam, hphi, u0ehi6, u0elo0]
                          · linarith only [h21, h31, h32, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · linarith only [h1, h27, h29, h3, h31, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                      · linarith only [h1, h23, h24, h27, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                    · linarith only [h1, h23, h25, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                · linarith only [h3, h42, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                  · linarith only [h21, h44, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                      · linarith only [h1, h24, h46, h47, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                            · linarith only [h21, h24, h49, h51, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                            · linarith only [h1, h21, h44, h46, h51, hc45, hlam, hphi, ht23, ht34, u0ehi6, u0elo0, u2ehi1]
                          · linarith only [h1, h3, h44, h46, h50, hc35, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                        · linarith only [h1, h3, h46, h49, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h1, h23, h42, h46, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                · linarith only [h3, h58, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                  · linarith only [h21, h60, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                    · linarith only [h1, h23, h3, h62, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                        · linarith only [h23, h3, h65, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h2, h3, h58, h62, h65, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                      · linarith only [h57, h58, h62, h64, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                · linarith only [h3, h69, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h1, h21, h69, h71, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h1, h23, h3, h73, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                      · linarith only [h2, h23, h3, h57, h75, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                        · linarith only [h23, h3, h77, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · linarith only [h2, h3, h69, h73, h77, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h80 | h80
        · rcases m.htr 0 2 4 (by decide) (by decide) with h81 | h81
          · linarith only [h0, h2, h81, hlam]
          · linarith only [h80, h81, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h84 | h84
          · linarith only [h80, h84, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h86 | h86
            · linarith only [h1, h2, h86, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                · linarith only [h0, h2, h89, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h84, h89, h91, hc13, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h1, h2, h89, h91, hc24, hlam, hphi, u2ehi1]
              · linarith only [h0, h2, h88, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
      · rcases m.htr 0 2 3 (by decide) (by decide) with h96 | h96
        · linarith only [h0, h1, h96, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h98 | h98
          · linarith only [h96, h98, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
            · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                · linarith only [h102, h96, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h1, h102, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
                · linarith only [h0, h105, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h0, h1, h105, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h100, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
        · linarith only [h0, h1, h109, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
          · linarith only [h109, h111, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h113 | h113
            · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                · linarith only [h0, h109, h115, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                · linarith only [h0, h1, h115, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h114, h95, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · linarith only [h0, h1, h113, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h120 | h120
    · rcases m.htr 0 1 4 (by decide) (by decide) with h121 | h121
      · rcases m.htr 0 2 3 (by decide) (by decide) with h122 | h122
        · rcases m.htr 0 2 4 (by decide) (by decide) with h123 | h123
          · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
            · rcases m.htr 0 4 5 (by decide) (by decide) with h125 | h125
              · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                              · linarith only [h120, h126, h130, h133, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h120, h128, h129, h133, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h0, h120, h128, h129, h132, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                            · linarith only [h130, h131, h137, hlam]
                            · linarith only [h124, h125, h137, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                        · linarith only [h0, h120, h124, h130, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h0, h120, h124, h125, h127, h129, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h0, h120, h124, h126, h128, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h127, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h120, h122, h124, h125, h126, hlam, hphi, u0ehi9, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                      · linarith only [h120, h125, h147, h148, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h151 | h151
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h152 | h152
                            · linarith only [h125, h150, h152, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h154 | h154
                              · linarith only [h0, h120, h125, h145, h150, h154, hc12, hlam, hphi, ht01, u0ehi8]
                              · rcases h4bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h125, hc14, hc45, hlam, hphi, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h125, hc24, hc45, hlam, hphi, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h125, hc34, hc45, hlam, hphi, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h125, hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h121, hlam, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h0, h121, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p156_1, u2ehi3]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h0, h120, h147, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h148, hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h123, hlam, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h146, hlam, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h123, hc34, hlam, hphi, ht0b, ht45, ht5b, p156_1, u0elo1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h152, hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h124, hlam, p156_1]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h147, hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h150, hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h154, hlam, p156_0]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p156_1, u0ehi8]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [h146, hc45, hlam, hphi, ht23, ht34, p156_1, u2ehi3]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht23, ht34, p156_1, u2ehi3]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  rcases p156_3 (m.d 0 4) (by simp) with h180 | h180
                                  · linarith only [h125, h180, hlam]
                                  · linarith only [h124, h180, hlam]
                                · have p156_0 := h156c.1
                                  have p156_1 := h156c.2.1
                                  have p156_2 := h156c.2.2.1
                                  have p156_3 := h156c.2.2.2
                                  linarith only [hlam, p156_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                            · linarith only [h125, h146, h184, hc14, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                              · linarith only [h0, h120, h125, h146, h147, h186, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi8, u2ehi3]
                              · rcases h4bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h146, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p188_1, u0elo3, u2ehi3]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h125, hc45, hlam, hphi, ht23, ht34, p188_1, u2ehi3]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h125, hc34, hc45, hlam, hphi, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h125, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h121, hlam, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h0, h120, h147, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p188_1, u2ehi3]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h0, h120, h147, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h148, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h123, hlam, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h146, hlam, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h123, hc34, hlam, hphi, ht0b, ht45, ht5b, p188_1, u0elo1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h184, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h124, hlam, p188_1]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h147, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h150, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h186, hlam, p188_0]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p188_1, u0ehi8]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [h146, hc45, hlam, hphi, ht23, ht34, p188_1, u2ehi3]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht23, ht34, p188_1, u2ehi3]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  rcases p188_3 (m.d 0 4) (by simp) with h212 | h212
                                  · linarith only [h125, h212, hlam]
                                  · linarith only [h124, h212, hlam]
                                · have p188_0 := h188c.1
                                  have p188_1 := h188c.2.1
                                  have p188_2 := h188c.2.2.1
                                  have p188_3 := h188c.2.2.2
                                  linarith only [hlam, p188_0]
                        · linarith only [h0, h120, h124, h150, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h120, h124, h145, h147, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h146, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h120, h124, h145, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
              · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                    · linarith only [h120, h124, h223, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                        · linarith only [h124, h226, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h229 | h229
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h230 | h230
                              · rcases h4bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h221, h223, h228, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p231_1, u0elo3, u2ehi4]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h0, h121, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p231_1, u2ehi3]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h124, hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  rcases p231_3 (m.d 0 4) (by simp) with h236 | h236
                                  · rcases p231_3 (m.d 1 4) (by simp) with h237 | h237
                                    · linarith only [h121, h237, hlam]
                                    · linarith only [h225, h237, hlam]
                                  · linarith only [h236, hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h121, hlam, p231_1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h0, h121, h226, h228, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p231_1, u2ehi4]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h223, hlam, p231_1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h0, h121, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p231_1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h123, hlam, p231_1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h222, hlam, p231_1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h226, hlam, p231_1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h123, hc45, hlam, hphi, ht0b, ht5b, p231_1, u0elo1]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p231_1, u0ehi8]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h222, hc34, hlam, hphi, ht23, p231_1, u2ehi3]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht23, p231_1, u2ehi3]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  rcases p231_3 (m.d 0 4) (by simp) with h255 | h255
                                  · linarith only [h124, h255, hlam]
                                  · linarith only [h220, h255, hlam]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h220, hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h225, hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h229, hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [h230, hlam, p231_0]
                                · have p231_0 := h231c.1
                                  have p231_1 := h231c.2.1
                                  have p231_2 := h231c.2.2.1
                                  have p231_3 := h231c.2.2.2
                                  linarith only [hlam, p231_0]
                              · linarith only [h0, h121, h124, h221, h223, h228, h230, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u2ehi4]
                            · linarith only [h0, h121, h225, h226, h228, h229, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                              · rcases h4bigk with h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c | h267c
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h0, h121, h221, h223, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p267_1, u2ehi2]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h0, h121, h228, h265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p267_1, u2ehi2]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h124, hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  rcases p267_3 (m.d 0 4) (by simp) with h272 | h272
                                  · rcases p267_3 (m.d 1 4) (by simp) with h273 | h273
                                    · linarith only [h121, h273, hlam]
                                    · linarith only [h225, h273, hlam]
                                  · linarith only [h272, hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h121, hlam, p267_1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h0, h121, h228, h265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p267_1, u2ehi2]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h223, hlam, p267_1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h0, h121, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p267_1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h123, hlam, p267_1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h222, hlam, p267_1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h226, hlam, p267_1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h123, hc45, hlam, hphi, ht0b, ht5b, p267_1, u0elo1]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p267_1, u0ehi8]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h222, hc34, hlam, hphi, ht23, p267_1, u2ehi3]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht23, p267_1, u2ehi3]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  rcases p267_3 (m.d 0 4) (by simp) with h291 | h291
                                  · linarith only [h124, h291, hlam]
                                  · linarith only [h220, h291, hlam]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h220, hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h225, hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h265, hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [h266, hlam, p267_0]
                                · have p267_0 := h267c.1
                                  have p267_1 := h267c.2.1
                                  have p267_2 := h267c.2.2.1
                                  have p267_3 := h267c.2.2.2
                                  linarith only [hlam, p267_0]
                              · linarith only [h0, h121, h124, h222, h228, h265, h266, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u2ehi2]
                            · linarith only [h0, h121, h225, h265, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h121, h220, h221, h223, h225, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h222, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h121, h124, h221, hc23, hlam, hphi, ht01, ht12, u0ehi7]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                · rcases m.htr 1 2 4 (by decide) (by decide) with h305 | h305
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                    · linarith only [h120, h124, h306, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                      · linarith only [h0, h121, h124, h220, h308, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                        · linarith only [h124, h310, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h313 | h313
                            · linarith only [h0, h121, h124, h220, h305, h313, hc12, hlam, hphi, ht01, u0ehi7]
                            · linarith only [h310, h312, h313, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h316 | h316
                            · linarith only [h124, h220, h316, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h318 | h318
                              · linarith only [h0, h121, h124, h220, h304, h306, h318, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi7, u2ehi2]
                              · linarith only [h0, h121, h124, h304, h306, h318, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u2ehi2]
                  · linarith only [h0, h305, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h121, h124, h304, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · linarith only [h122, h123, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h120, h122, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h325 | h325
        · rcases m.htr 0 2 4 (by decide) (by decide) with h326 | h326
          · rcases m.htr 0 3 4 (by decide) (by decide) with h327 | h327
            · linarith only [h120, h121, h327, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
              · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                    · linarith only [h120, h327, h332, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h120, h121, h330, h332, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h326, h331, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h325, h330, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
                · linarith only [h120, h121, h329, h337, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h120, h337, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · linarith only [h325, h326, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h120, h325, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h342 | h342
      · rcases m.htr 0 2 3 (by decide) (by decide) with h343 | h343
        · rcases m.htr 0 2 4 (by decide) (by decide) with h344 | h344
          · rcases m.htr 0 3 4 (by decide) (by decide) with h345 | h345
            · rcases m.htr 0 4 5 (by decide) (by decide) with h346 | h346
              · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h351 | h351
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h352 | h352
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h353 | h353
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h354 | h354
                              · linarith only [h343, h351, h354, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h120, h342, h343, h350, h354, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h120, h342, h343, h350, h353, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                            · linarith only [h351, h352, h358, hlam]
                            · linarith only [h346, h358, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                        · linarith only [h343, h345, h351, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h120, h342, h343, h346, h348, h350, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                    · linarith only [h120, h349, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h120, h347, h348, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h343, h347, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h366 | h366
                · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                      · linarith only [h342, h346, h369, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h371 | h371
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h372 | h372
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h373 | h373
                            · linarith only [h346, h373, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h375 | h375
                              · linarith only [h343, h346, h371, h375, hlam, hphi, u0ehi8, u0elo1]
                              · rcases h4bigk with h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h367, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p377_1, u0elo3, u2ehi3]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h346, hc45, hlam, hphi, ht23, ht34, p377_1, u2ehi3]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h346, hc34, hc45, hlam, hphi, p377_1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h346, hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h342, hlam, p377_1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h120, h342, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p377_1, u2ehi3]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h120, h342, h366, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p377_1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h369, hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h344, hlam, p377_1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h367, hlam, p377_1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h344, hc34, hlam, hphi, ht0b, ht45, ht5b, p377_1, u0elo1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h373, hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h345, hlam, p377_1]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h368, hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h371, hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h375, hlam, p377_0]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p377_1, u0ehi8]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [h367, hc45, hlam, hphi, ht23, ht34, p377_1, u2ehi3]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht23, ht34, p377_1, u2ehi3]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  rcases p377_3 (m.d 0 4) (by simp) with h401 | h401
                                  · linarith only [h346, h401, hlam]
                                  · linarith only [h345, h401, hlam]
                                · have p377_0 := h377c.1
                                  have p377_1 := h377c.2.1
                                  have p377_2 := h377c.2.2.1
                                  have p377_3 := h377c.2.2.2
                                  linarith only [hlam, p377_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                            · linarith only [h120, h342, h346, h366, h367, h405, hc12, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                              · linarith only [h120, h342, h346, h366, h367, h407, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi8, u2ehi3]
                              · rcases h4bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h367, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p409_1, u0elo3, u2ehi3]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h346, hc45, hlam, hphi, ht23, ht34, p409_1, u2ehi3]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h346, hc34, hc45, hlam, hphi, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h346, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h342, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h120, h342, h366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u2ehi3]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h120, h342, h366, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h369, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h344, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h367, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h344, hc34, hlam, hphi, ht0b, ht45, ht5b, p409_1, u0elo1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h405, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h345, hlam, p409_1]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h368, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h371, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h407, hlam, p409_0]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p409_1, u0ehi8]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [h367, hc45, hlam, hphi, ht23, ht34, p409_1, u2ehi3]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht23, ht34, p409_1, u2ehi3]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  rcases p409_3 (m.d 0 4) (by simp) with h433 | h433
                                  · linarith only [h346, h433, hlam]
                                  · linarith only [h345, h433, hlam]
                                · have p409_0 := h409c.1
                                  have p409_1 := h409c.2.1
                                  have p409_2 := h409c.2.2.1
                                  have p409_3 := h409c.2.2.2
                                  linarith only [hlam, p409_0]
                        · linarith only [h343, h345, h371, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h120, h343, h345, h368, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h120, h342, h366, h367, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                · linarith only [h0, h342, h366, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h120, h342, h345, hlam]
          · linarith only [h343, h344, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h443 | h443
          · linarith only [h343, h443, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h342, h443, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h446 | h446
        · rcases m.htr 0 2 4 (by decide) (by decide) with h447 | h447
          · rcases m.htr 0 3 4 (by decide) (by decide) with h448 | h448
            · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
              · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
                              · linarith only [h446, h454, h457, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h446, h454, h456, h457, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h448, h449, h456, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h454, h455, h461, hlam]
                            · linarith only [h446, h448, h449, h461, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                        · linarith only [h446, h448, h454, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h342, h446, h448, h449, h453, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h120, h446, h448, h452, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h120, h450, h451, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h450, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
                · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h472 | h472
                      · linarith only [h449, h469, h471, h472, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h342, h472, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                    · linarith only [h120, h446, h448, h471, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h447, h470, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h446, h469, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h478 | h478
              · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                · rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
                    · linarith only [h448, h479, h481, hc12, hlam, hphi, ht01, u0ehi7]
                    · linarith only [h120, h481, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h447, h480, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h446, h479, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
                · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                    · linarith only [h120, h448, h486, h488, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h120, h488, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h120, h447, h448, h478, h487, hc45, hlam, hphi, ht23, ht34, u0ehi5, u0elo1, u2ehi1]
                · linarith only [h0, h446, h486, hlam, hphi, u0ehi5, u0elo1]
          · linarith only [h446, h447, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h494 | h494
          · linarith only [h446, h494, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h496 | h496
            · rcases m.htr 0 4 5 (by decide) (by decide) with h497 | h497
              · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
                · linarith only [h446, h498, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h498, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
                · linarith only [h0, h446, h501, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h501, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h504 | h504
              · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
                · linarith only [h0, h446, h505, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h505, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
                · linarith only [h0, h446, h508, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h508, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
