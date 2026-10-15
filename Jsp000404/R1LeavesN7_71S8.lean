import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_R_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h10, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h13, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                      · linarith only [h17, h5, h8, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h19, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h16, h19, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                      · linarith only [h22, h5, h8, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h0, h16, h2, h24, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                          · linarith only [h16, h26, h5, h8, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h26, h5, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h5, h7, hc25, hlam, hphi, u2ehi2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
              · linarith only [h31, h5, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h2, h31, h33, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                          · rcases h4bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, h35, h39, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, h33, h38, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u2ehi1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, h39, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              rcases p40_3 (m.d 0 4) (by simp) with h45 | h45
                              · rcases p40_3 (m.d 1 4) (by simp) with h46 | h46
                                · linarith only [h1, h46, hlam]
                                · linarith only [h36, h46, hlam]
                              · linarith only [h45, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h1, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h31, hlam, p40_1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h39, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, h31, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h2, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, h39, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h3, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h35, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h37, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h1, h35, hc01, hlam, hphi, ht0b, ht45, ht5b, p40_1, u4ehi4]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h4, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h36, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h38, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h39, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                          · linarith only [h0, h2, h31, h36, h39, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h31, h36, h38, hlam]
                      · linarith only [h3, h37, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                        · linarith only [h0, h2, h36, h74, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h0, h2, h31, h4, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · linarith only [h35, h5, h73, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                      · linarith only [h35, h5, h79, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h5, h79, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                      · linarith only [h35, h5, h82, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h5, h82, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
            · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h1, h4, h89, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                      · linarith only [h0, h85, h91, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h3, h4, h91, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h3, h4, h85, h88, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h85, h87, hc25, hlam, hphi, u2ehi2]
              · linarith only [h85, h86, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
              · linarith only [h85, h97, hc23, hlam, hphi, u2ehi3]
              · linarith only [h2, h4, h97, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
          · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
            · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h0, h100, h101, h104, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                      · linarith only [h101, h104, h107, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h102, h109, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h106, h109, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h100, h102, h106, h3, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h101, h103, hc25, hlam, hphi, u2ehi2]
              · linarith only [h101, h102, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
              · linarith only [h101, h115, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                · linarith only [h0, h115, h117, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                  · linarith only [h101, h115, h119, h2, h3, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                      · linarith only [h115, h122, h2, h3, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h101, h122, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h100, h115, h121, h3, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h126 | h126
            · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
              · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                  · linarith only [h1, h129, h3, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                    · linarith only [h1, h100, h131, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h0, h126, h133, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h100, h135, h2, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h137 | h137
                          · linarith only [h1, h100, h126, h129, h137, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h126, h129, h137, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h126, h128, hc25, hlam, hphi, u2ehi2]
              · linarith only [h126, h127, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
              · linarith only [h126, h142, hc23, hlam, hphi, u2ehi3]
              · linarith only [h100, h142, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h145 | h145
        · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
          · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
            · linarith only [h0, h147, h2, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
              · linarith only [h0, h149, h2, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
                · linarith only [h0, h151, h2, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                          · rcases h4bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h151, h154, h155, h2, hc23, hlam, hphi, p158_1, u2ehi1]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h2, hlam, p158_1]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h155, h157, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p158_1, u4ehi4]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              rcases p158_3 (m.d 0 4) (by simp) with h163 | h163
                              · rcases p158_3 (m.d 1 4) (by simp) with h164 | h164
                                · linarith only [h1, h164, hlam]
                                · linarith only [h154, h164, hlam]
                              · linarith only [h163, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h1, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h149, hlam, p158_1]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h157, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1, u4ehi4]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p158_1, u4ehi4]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h0, h155, h2, hc23, hlam, hphi, p158_1, u2ehi1]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h149, h155, hc23, hlam, hphi, p158_1, u2ehi1]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h155, h157, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p158_1, u4ehi4]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              rcases p158_3 (m.d 0 4) (by simp) with h177 | h177
                              · linarith only [h177, h2, hlam]
                              · linarith only [h146, h177, hlam]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h145, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h153, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h155, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h145, hc03, hlam, hphi, ht0b, ht45, ht5b, p158_1, u4ehi4]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h146, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h154, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h156, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [h157, hlam, p158_0]
                            · have p158_0 := h158c.1
                              have p158_1 := h158c.2.1
                              have p158_2 := h158c.2.2.1
                              have p158_3 := h158c.2.2.2
                              linarith only [hlam, p158_0]
                          · linarith only [h1, h154, h157, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h154, h156, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h145, h147, h155, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h146, h149, h154, h2, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h147, h153, h195, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h147, h195, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h146, h149, h194, h2, hc24, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
            · linarith only [h0, h199, h2, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
              · linarith only [h0, h146, h2, h201, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                · linarith only [h0, h146, h2, h203, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h206 | h206
                    · linarith only [h1, h146, h2, h206, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                        · linarith only [h0, h146, h2, h208, h209, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h209, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                      · linarith only [h145, h146, h208, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h145, h146, h199, h205, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h214 | h214
          · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
            · linarith only [h0, h2, h215, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
              · linarith only [h215, h217, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                · linarith only [h0, h2, h219, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h1, h145, h221, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                      · linarith only [h215, h221, h224, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h215, h224, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h2, h214, h217, h223, hc24, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
            · linarith only [h0, h2, h214, h228, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
              · linarith only [h0, h2, h214, h230, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                · linarith only [h0, h2, h214, h232, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                  · linarith only [h1, h145, h234, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                    · linarith only [h1, h214, h236, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h238 | h238
                      · linarith only [h228, h234, h238, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h228, h238, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h241 | h241
      · linarith only [h0, h1, h241, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
        · rcases m.htr 0 4 5 (by decide) (by decide) with h244 | h244
          · rcases m.htr 1 2 3 (by decide) (by decide) with h245 | h245
            · linarith only [h0, h1, h245, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
              · linarith only [h0, h1, h241, h247, hlam]
              · linarith only [h0, h1, h247, hc24, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h244, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
          · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
            · linarith only [h0, h1, h252, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h254 | h254
              · linarith only [h0, h1, h254, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1, h254, hc24, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h251, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h258 | h258
    · rcases m.htr 0 2 4 (by decide) (by decide) with h259 | h259
      · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
        · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
          · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
            · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
              · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                    · linarith only [h0, h258, h266, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h258, h261, h263, h266, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                    · linarith only [h0, h258, h269, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h258, h261, h269, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h258, h261, h264, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h258, h259, h263, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · linarith only [h0, h258, h261, h262, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
            · rcases m.htr 1 2 4 (by decide) (by decide) with h276 | h276
              · rcases m.htr 1 2 5 (by decide) (by decide) with h277 | h277
                · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
                    · linarith only [h258, h261, h279, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h0, h258, h276, h277, h279, h282, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                          · linarith only [h258, h261, h276, h284, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h4bigk with h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h261, h276, hc45, hlam, hphi, ht23, ht34, p286_1, u2ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h261, hc45, hlam, hphi, ht23, ht34, p286_1, u2ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h261, hc45, hlam, hphi, p286_1, u4ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h261, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h258, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h258, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p286_1, u2ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h0, h258, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1, u4ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h279, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h259, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h276, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h0, h259, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1, u4ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h282, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h260, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h278, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h281, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [h284, hlam, p286_0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hc45, hlam, hphi, p286_1, u4ehi0]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hc45, hlam, hphi, p286_1, u4ehi1]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p286_1, u2ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hc45, hlam, hphi, p286_1, u4ehi3]
                            · have p286_0 := h286c.1
                              have p286_1 := h286c.2.1
                              have p286_2 := h286c.2.2.1
                              have p286_3 := h286c.2.2.2
                              linarith only [hlam, p286_0]
                      · linarith only [h260, h261, h281, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h260, h261, h275, h278, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h258, h276, h277, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h258, h276, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h258, h275, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
          · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
            · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
              · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                  · linarith only [h0, h258, h260, h317, h321, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                    · linarith only [h0, h258, h323, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h258, h317, h318, h321, h323, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h258, h317, h320, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h258, h317, h319, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h258, h317, h318, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
            · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
              · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                  · linarith only [h258, h260, h332, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                    · linarith only [h0, h258, h334, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                      · linarith only [h0, h258, h329, h332, h336, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                        · linarith only [h258, h317, h330, h338, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                          · linarith only [h258, h317, h329, h332, h340, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h329, h332, h340, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h258, h331, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h258, h259, h330, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h0, h258, h329, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h258, h259, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h347 | h347
      · rcases m.htr 0 3 4 (by decide) (by decide) with h348 | h348
        · rcases m.htr 0 4 5 (by decide) (by decide) with h349 | h349
          · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
            · rcases m.htr 1 2 4 (by decide) (by decide) with h351 | h351
              · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
                · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h356 | h356
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h357 | h357
                          · linarith only [h350, h355, h357, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h347, h356, h357, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h360 | h360
                          · linarith only [h356, h360, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h4bigk with h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h258, hlam, p362_1]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              rcases p362_3 (m.d 0 4) (by simp) with h365 | h365
                              · rcases p362_3 (m.d 1 4) (by simp) with h366 | h366
                                · rcases p362_3 (m.d 2 4) (by simp) with h367 | h367
                                  · linarith only [h347, h367, hlam]
                                  · rcases p362_3 (m.d 3 4) (by simp) with h369 | h369
                                    · linarith only [h348, h369, hlam]
                                    · rcases p362_3 (m.d 4 5) (by simp) with h371 | h371
                                      · linarith only [h349, h371, hlam]
                                      · linarith only [h356, h371, hlam]
                                · linarith only [h351, h366, hlam]
                              · linarith only [h347, h365, hlam]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              rcases p362_3 (m.d 0 4) (by simp) with h376 | h376
                              · rcases p362_3 (m.d 1 4) (by simp) with h377 | h377
                                · rcases p362_3 (m.d 2 4) (by simp) with h378 | h378
                                  · linarith only [h347, h378, hlam]
                                  · linarith only [h355, h378, hlam]
                                · linarith only [h353, h377, hlam]
                              · linarith only [h348, h376, hlam]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h356, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p362_1, u2ehi3]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h349, h350, h353, h356, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p362_1, u2ehi3]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              rcases p362_3 (m.d 0 4) (by simp) with h386 | h386
                              · linarith only [h258, h386, hlam]
                              · linarith only [h347, h386, hlam]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              rcases p362_3 (m.d 0 4) (by simp) with h389 | h389
                              · linarith only [h258, h389, hlam]
                              · linarith only [h348, h389, hlam]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h350, h353, h356, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p362_1, u2ehi3]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h347, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h351, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h349, h356, hc04, hlam, hphi, ht0b, ht45, ht5b, p362_1, u4ehi3]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h356, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h348, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h353, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h355, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h360, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h349, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h354, hlam, p362_0]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h349, hc04, hlam, hphi, ht0b, ht45, ht5b, p362_1, u4ehi2]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [h258, h349, h350, h353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p362_1, u4ehi3]
                            · have p362_0 := h362c.1
                              have p362_1 := h362c.2.1
                              have p362_2 := h362c.2.2.1
                              have p362_3 := h362c.2.2.2
                              linarith only [hlam, p362_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                          · rcases h4bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h258, hlam, p410_1]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h258, h350, h353, h408, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p410_1, u4ehi4]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h258, h350, h353, h355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi2]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              rcases p410_3 (m.d 0 4) (by simp) with h415 | h415
                              · rcases p410_3 (m.d 1 4) (by simp) with h416 | h416
                                · rcases p410_3 (m.d 2 4) (by simp) with h417 | h417
                                  · linarith only [h347, h417, hlam]
                                  · linarith only [h408, h417, hlam]
                                · linarith only [h354, h416, hlam]
                              · linarith only [h415, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h347, h350, h353, h408, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p410_1, u4ehi4]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h350, h353, h408, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p410_1, u4ehi4]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h350, h353, h355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi2]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              rcases p410_3 (m.d 0 4) (by simp) with h426 | h426
                              · linarith only [h258, h426, hlam]
                              · linarith only [h349, h426, hlam]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h347, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h351, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h355, hlam, p410_1]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h0, h347, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p410_1, u4ehi4]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h348, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h353, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [hc34, hlam, hphi, ht23, p410_1, u2ehi3]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h350, h353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p410_1, u4ehi4]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h349, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h354, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h408, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [h409, hlam, p410_0]
                            · have p410_0 := h410c.1
                              have p410_1 := h410c.2.1
                              have p410_2 := h410c.2.2.1
                              have p410_3 := h410c.2.2.2
                              linarith only [hlam, p410_0]
                          · linarith only [h0, h347, h408, h409, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h445 | h445
                          · linarith only [h355, h408, h445, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h349, h355, h445, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h258, h349, h354, hlam]
                  · linarith only [h258, h348, h353, hlam]
                · linarith only [h0, h347, h352, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h347, h351, hlam]
            · linarith only [h0, h347, h350, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h453 | h453
            · rcases m.htr 1 2 4 (by decide) (by decide) with h454 | h454
              · rcases m.htr 1 2 5 (by decide) (by decide) with h455 | h455
                · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                        · linarith only [h347, h349, h459, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                          · linarith only [h347, h349, h458, h461, hlam]
                          · rcases h4bigk with h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h258, hlam, p463_1]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h349, h453, h456, h457, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p463_1, u2ehi3]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h349, h453, h456, h457, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p463_1, u4ehi3]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h349, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              rcases p463_3 (m.d 0 4) (by simp) with h469 | h469
                              · linarith only [h258, h469, hlam]
                              · rcases p463_3 (m.d 1 4) (by simp) with h471 | h471
                                · rcases p463_3 (m.d 2 4) (by simp) with h472 | h472
                                  · linarith only [h454, h472, hlam]
                                  · rcases p463_3 (m.d 3 4) (by simp) with h474 | h474
                                    · linarith only [h456, h474, hlam]
                                    · rcases p463_3 (m.d 4 5) (by simp) with h476 | h476
                                      · linarith only [h457, h476, hlam]
                                      · linarith only [h349, h476, hlam]
                                · linarith only [h258, h471, hlam]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              rcases p463_3 (m.d 0 4) (by simp) with h481 | h481
                              · linarith only [h258, h481, hlam]
                              · linarith only [h347, h481, hlam]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              rcases p463_3 (m.d 0 4) (by simp) with h484 | h484
                              · linarith only [h258, h484, hlam]
                              · linarith only [h348, h484, hlam]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h349, h453, h456, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p463_1, u4ehi0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h347, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h454, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h347, h349, hc45, hlam, hphi, p463_1, u4ehi3]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h459, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h348, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h456, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h458, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h461, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [hc45, hlam, hphi, p463_1, u4ehi0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h457, hlam, p463_0]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h453, h456, h457, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p463_1, u2ehi3]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [h453, h456, h457, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p463_1, u4ehi3]
                            · have p463_0 := h463c.1
                              have p463_1 := h463c.2.1
                              have p463_2 := h463c.2.2.1
                              have p463_3 := h463c.2.2.2
                              linarith only [hlam, p463_0]
                      · linarith only [h348, h349, h453, h456, h457, h458, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h505 | h505
                        · linarith only [h258, h457, h505, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                          · linarith only [h258, h453, h457, h504, h507, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases h4bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h258, hlam, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h258, h457, hc45, hlam, hphi, p509_1, u4ehi2]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h258, h457, hc45, hlam, hphi, p509_1, u4ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h349, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h457, hc45, hlam, hphi, p509_1, u4ehi0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h457, hc45, hlam, hphi, ht23, ht34, p509_1, u2ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h457, hc45, hlam, hphi, p509_1, u4ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h457, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h347, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h454, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h258, h347, h457, hc45, hlam, hphi, p509_1, u4ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h505, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h348, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h456, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h504, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h507, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc45, hlam, hphi, p509_1, u4ehi0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc45, hlam, hphi, p509_1, u4ehi1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p509_1, u2ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc45, hlam, hphi, p509_1, u4ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                      · linarith only [h348, h349, h504, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h348, h349, h453, h456, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h347, h455, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h347, h454, hlam]
            · linarith only [h0, h347, h453, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h540 | h540
          · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
            · rcases m.htr 1 2 4 (by decide) (by decide) with h542 | h542
              · rcases m.htr 1 2 5 (by decide) (by decide) with h543 | h543
                · rcases m.htr 1 3 4 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h545 | h545
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h546 | h546
                      · linarith only [h348, h540, h541, h546, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h548 | h548
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                          · rcases h4bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h258, hlam, p550_1]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h548, hc04, hlam, hphi, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h348, hlam, p550_1]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h348, h544, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h347, h548, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h542, h548, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h347, h348, h541, h544, h548, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              rcases p550_3 (m.d 0 4) (by simp) with h560 | h560
                              · linarith only [h258, h560, hlam]
                              · linarith only [h540, h560, hlam]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h347, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h542, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h546, hlam, p550_1]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h347, hc02, hlam, hphi, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h347, hc34, hlam, hphi, ht23, p550_1, u2ehi3]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h544, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h541, h544, h548, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p550_1, u2ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h541, h544, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p550_1, u4ehi4]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h540, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h545, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h548, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [h549, hlam, p550_0]
                            · have p550_0 := h550c.1
                              have p550_1 := h550c.2.1
                              have p550_2 := h550c.2.2.1
                              have p550_3 := h550c.2.2.2
                              linarith only [hlam, p550_0]
                          · linarith only [h0, h347, h348, h548, h549, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h348, h540, h541, h544, h548, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h348, h540, h541, h544, h545, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h581 | h581
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                      · linarith only [h258, h540, h541, h544, h582, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h584 | h584
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h585 | h585
                          · rcases h4bigk with h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h258, hlam, p586_1]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h584, hc04, hlam, hphi, ht0b, ht45, ht5b, p586_1, u4ehi4]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h348, hlam, p586_1]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              rcases p586_3 (m.d 0 4) (by simp) with h591 | h591
                              · rcases p586_3 (m.d 1 4) (by simp) with h592 | h592
                                · rcases p586_3 (m.d 2 4) (by simp) with h593 | h593
                                  · linarith only [h347, h593, hlam]
                                  · linarith only [h584, h593, hlam]
                                · linarith only [h581, h592, hlam]
                              · linarith only [h591, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h347, h544, h584, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p586_1, u4ehi4]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h544, h584, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p586_1, u4ehi4]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h544, hlam, p586_1]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              rcases p586_3 (m.d 0 4) (by simp) with h602 | h602
                              · linarith only [h258, h602, hlam]
                              · linarith only [h540, h602, hlam]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h347, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h542, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h582, hlam, p586_1]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h0, h347, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p586_1, u4ehi4]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h347, hc34, hlam, hphi, ht23, p586_1, u2ehi3]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h258, hc01, hc34, hlam, hphi, ht12, ht23, p586_1]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [hc34, hlam, hphi, ht23, p586_1, u2ehi3]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              rcases p586_3 (m.d 0 4) (by simp) with h614 | h614
                              · linarith only [h348, h614, hlam]
                              · linarith only [h540, h614, hlam]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h540, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h581, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h584, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [h585, hlam, p586_0]
                            · have p586_0 := h586c.1
                              have p586_1 := h586c.2.1
                              have p586_2 := h586c.2.2.1
                              have p586_3 := h586c.2.2.2
                              linarith only [hlam, p586_0]
                          · linarith only [h0, h347, h584, h585, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h258, h540, h544, h584, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h258, h540, h581, hlam]
                · linarith only [h0, h347, h543, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h347, h542, hlam]
            · linarith only [h0, h347, h541, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
            · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
              · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                · rcases m.htr 1 3 4 (by decide) (by decide) with h631 | h631
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h632 | h632
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h633 | h633
                      · linarith only [h347, h348, h633, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h635 | h635
                        · linarith only [h347, h540, h635, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h637 | h637
                          · linarith only [h347, h540, h637, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h628, h631, h632, h633, h637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                      · linarith only [h347, h348, h640, hlam]
                      · linarith only [h631, h632, h640, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h643 | h643
                    · linarith only [h347, h540, h631, h643, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
                      · linarith only [h628, h631, h645, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                        · linarith only [h347, h643, h647, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                          · linarith only [h258, h347, h643, h645, h649, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h628, h631, h649, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h347, h630, hc25, hlam, hphi, u2ehi3]
              · linarith only [h0, h347, h629, hlam]
            · linarith only [h0, h347, h628, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h655 | h655
        · rcases m.htr 0 4 5 (by decide) (by decide) with h656 | h656
          · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
            · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
              · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
                · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h663 | h663
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h664 | h664
                          · linarith only [h657, h662, h664, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h347, h656, h658, h664, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h347, h656, h663, hlam]
                      · linarith only [h347, h655, h662, hlam]
                    · linarith only [h347, h656, h658, h661, hlam]
                  · linarith only [h347, h655, h658, h660, hlam]
                · linarith only [h657, h659, hc25, hlam, hphi, u2ehi2]
              · linarith only [h657, h658, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h673 | h673
              · linarith only [h657, h673, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
                · linarith only [h657, h675, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h681 | h681
                          · rcases h4bigk with h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h258, hlam, p682_1]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h347, hlam, p682_1]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h681, hc04, hlam, hphi, ht0b, ht45, ht5b, p682_1, u4ehi4]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              rcases p682_3 (m.d 0 4) (by simp) with h687 | h687
                              · rcases p682_3 (m.d 1 4) (by simp) with h688 | h688
                                · rcases p682_3 (m.d 2 4) (by simp) with h689 | h689
                                  · rcases p682_3 (m.d 3 4) (by simp) with h690 | h690
                                    · linarith only [h655, h690, hlam]
                                    · linarith only [h681, h690, hlam]
                                  · linarith only [h680, h689, hlam]
                                · linarith only [h678, h688, hlam]
                              · linarith only [h687, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h347, h673, h679, hc23, hlam, hphi, p682_1, u2ehi0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h673, hlam, p682_1]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h673, h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p682_1, u4ehi4]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              rcases p682_3 (m.d 0 4) (by simp) with h700 | h700
                              · linarith only [h258, h700, hlam]
                              · linarith only [h656, h700, hlam]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h655, h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p682_1, u4ehi4]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h258, h679, hc01, hc23, hlam, hphi, ht12, p682_1]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p682_1, u4ehi4]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              rcases p682_3 (m.d 0 4) (by simp) with h707 | h707
                              · linarith only [h347, h707, hlam]
                              · linarith only [h656, h707, hlam]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h655, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h677, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h679, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h677, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p682_1, u4ehi4]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h656, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h678, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h680, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [h681, hlam, p682_0]
                            · have p682_0 := h682c.1
                              have p682_1 := h682c.2.1
                              have p682_2 := h682c.2.2.1
                              have p682_3 := h682c.2.2.2
                              linarith only [hlam, p682_0]
                          · rcases h4bigk with h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h258, hlam, p720_1]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h347, hlam, p720_1]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              rcases p720_3 (m.d 0 4) (by simp) with h724 | h724
                              · rcases p720_3 (m.d 1 4) (by simp) with h725 | h725
                                · rcases p720_3 (m.d 2 4) (by simp) with h726 | h726
                                  · rcases p720_3 (m.d 3 4) (by simp) with h727 | h727
                                    · linarith only [h655, h727, hlam]
                                    · rcases p720_3 (m.d 4 5) (by simp) with h729 | h729
                                      · linarith only [h656, h729, hlam]
                                      · linarith only [h681, h729, hlam]
                                  · linarith only [h679, h726, hlam]
                                · linarith only [h677, h725, hlam]
                              · linarith only [h655, h724, hlam]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h258, h673, h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u4ehi3]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h347, h673, h679, hc23, hlam, hphi, p720_1, u2ehi0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h673, hlam, p720_1]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              rcases p720_3 (m.d 0 4) (by simp) with h739 | h739
                              · linarith only [h258, h739, hlam]
                              · linarith only [h655, h739, hlam]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h673, h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u4ehi3]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h656, h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u4ehi3]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h258, h679, hc01, hc23, hlam, hphi, ht12, p720_1]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              rcases p720_3 (m.d 0 4) (by simp) with h746 | h746
                              · linarith only [h347, h746, hlam]
                              · linarith only [h655, h746, hlam]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h679, h681, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p720_1, u4ehi3]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h655, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h677, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h679, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h681, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h656, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h678, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h680, hlam, p720_0]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [h656, hc04, hlam, hphi, ht0b, ht45, ht5b, p720_1, u4ehi3]
                            · have p720_0 := h720c.1
                              have p720_1 := h720c.2.1
                              have p720_2 := h720c.2.2.1
                              have p720_3 := h720c.2.2.2
                              linarith only [hlam, p720_0]
                        · linarith only [h258, h656, h673, h680, hlam]
                      · linarith only [h0, h258, h655, h657, h679, hc01, hc14, hlam, hphi]
                    · linarith only [h258, h656, h678, hlam]
                  · linarith only [h258, h655, h677, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
            · rcases m.htr 1 2 4 (by decide) (by decide) with h765 | h765
              · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                · rcases m.htr 1 3 4 (by decide) (by decide) with h767 | h767
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h768 | h768
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h769 | h769
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                        · linarith only [h347, h656, h770, hc24, hlam, hphi, u2ehi0]
                        · linarith only [h347, h764, h767, h768, h770, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h655, h656, h764, h767, h768, h769, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h347, h765, h768, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h655, h656, h764, h767, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h764, h766, hc25, hlam, hphi, u2ehi2]
              · linarith only [h764, h765, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h778 | h778
              · linarith only [h764, h778, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h780 | h780
                · linarith only [h764, h780, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h782 | h782
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h783 | h783
                    · linarith only [h347, h656, h764, h782, h783, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h785 | h785
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h786 | h786
                        · linarith only [h778, h783, h786, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h347, h786, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h655, h656, h785, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h655, h656, h764, h782, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h791 | h791
          · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
            · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
              · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
                      · linarith only [h655, h791, h792, h797, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h799 | h799
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h800 | h800
                          · rcases h4bigk with h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c | h801c
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h258, hlam, p801_1]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h347, hlam, p801_1]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h655, hlam, p801_1]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h347, h792, h795, h797, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h791, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h347, h793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p801_1, u2ehi0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h655, h791, h792, h795, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              rcases p801_3 (m.d 0 4) (by simp) with h811 | h811
                              · linarith only [h258, h811, hlam]
                              · linarith only [h791, h811, hlam]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h791, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h793, hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h797, hlam, p801_1]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h792, h795, h797, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h791, h792, h795, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h795, hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h347, h792, h795, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p801_1, u2ehi0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h792, h795, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p801_1, u4ehi4]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h791, hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h796, hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h799, hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [h800, hlam, p801_0]
                            · have p801_0 := h801c.1
                              have p801_1 := h801c.2.1
                              have p801_2 := h801c.2.2.1
                              have p801_3 := h801c.2.2.2
                              linarith only [hlam, p801_0]
                          · linarith only [h791, h797, h800, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h347, h791, h799, hlam]
                    · linarith only [h258, h347, h791, h796, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                      · linarith only [h655, h791, h792, h833, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h836 | h836
                          · rcases h4bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h258, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h347, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h655, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h347, h793, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p837_1, u4ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h347, h795, hc34, hlam, hphi, ht23, p837_1, u2ehi0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h795, hc34, hlam, hphi, ht23, p837_1, u2ehi3]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h795, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              rcases p837_3 (m.d 0 4) (by simp) with h847 | h847
                              · linarith only [h258, h847, hlam]
                              · linarith only [h791, h847, hlam]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h791, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p837_1, u4ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h793, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h833, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h793, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p837_1, u4ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h791, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p837_1, u4ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h258, hc01, hc34, hlam, hphi, ht12, ht23, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h347, hc34, hlam, hphi, ht23, p837_1, u2ehi0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              rcases p837_3 (m.d 0 4) (by simp) with h859 | h859
                              · linarith only [h655, h859, hlam]
                              · linarith only [h791, h859, hlam]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h791, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h832, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h835, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h836, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                          · linarith only [h655, h791, h836, hlam]
                        · linarith only [h347, h791, h835, hlam]
                    · linarith only [h347, h791, h793, h832, hlam]
                · linarith only [h793, h794, hc25, hlam, hphi, u2ehi3]
              · linarith only [h792, h793, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h872 | h872
              · linarith only [h792, h872, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
                · linarith only [h792, h874, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h877 | h877
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h878 | h878
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h879 | h879
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h880 | h880
                          · rcases h4bigk with h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h258, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h347, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h655, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h655, h876, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h791, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h872, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h655, h791, h872, h878, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              rcases p881_3 (m.d 0 4) (by simp) with h891 | h891
                              · linarith only [h258, h891, hlam]
                              · linarith only [h791, h891, hlam]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h791, h878, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h258, h878, hc01, hc23, hlam, hphi, ht12, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h655, h791, h878, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              rcases p881_3 (m.d 0 4) (by simp) with h898 | h898
                              · linarith only [h347, h898, hlam]
                              · linarith only [h791, h898, hlam]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h791, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h876, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h878, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h792, h876, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p881_1, u4ehi4]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h791, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h877, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h879, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h880, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                          · linarith only [h655, h791, h880, hlam]
                        · linarith only [h655, h791, h792, h876, h879, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h792, h876, h878, hlam]
                    · linarith only [h655, h791, h792, h876, h877, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h915 | h915
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h916 | h916
                      · linarith only [h0, h792, h876, h916, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h0, h792, h916, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h258, h791, h915, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h920 | h920
            · rcases m.htr 1 2 4 (by decide) (by decide) with h921 | h921
              · rcases m.htr 1 2 5 (by decide) (by decide) with h922 | h922
                · rcases m.htr 1 3 4 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h925 | h925
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                        · linarith only [h347, h791, h926, hc24, hlam, hphi, u2ehi0]
                        · linarith only [h347, h920, h923, h924, h926, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h929 | h929
                        · linarith only [h347, h791, h929, hc24, hlam, hphi, u2ehi0]
                        · linarith only [h347, h920, h923, h924, h929, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h347, h921, h924, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h933 | h933
                    · linarith only [h347, h791, h923, h933, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h347, h921, h933, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · linarith only [h347, h921, h922, hc25, hlam, hphi, u2ehi0]
              · linarith only [h920, h921, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h938 | h938
              · linarith only [h920, h938, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h940 | h940
                · linarith only [h920, h940, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h943 | h943
                    · linarith only [h347, h791, h938, h943, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h945 | h945
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h946 | h946
                        · linarith only [h938, h943, h945, h946, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h347, h946, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h0, h920, h942, h945, hc01, hc14, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                    · linarith only [h347, h791, h942, h950, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                      · linarith only [h0, h920, h942, h952, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h920, h952, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
