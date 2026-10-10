import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB2_H_I_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h13, h16, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h16, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h12, h15, h2, hc24, hlam, hphi, ht45, u5elo0]
                              · linarith only [h14, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h13, h21, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h21, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h12, hc14, hlam, hphi, ht45, u5elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                            · linarith only [h11, h26, h8, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                              · linarith only [h11, h28, h3, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h28, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h25, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h10, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h4, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h7, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                        · linarith only [h1, h40, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                            · linarith only [h3, h43, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                                  · rcases h4bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p48_1, u2elo0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h4, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p48_1, u2elo0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h6, hlam, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h1, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h43, h45, h47, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h40, hlam, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h4, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h38, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h43, hlam, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo3]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h3, h45, h47, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h40, hc13, hc34, hlam, hphi, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h43, h45, h47, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p48_1]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      rcases p48_3 (m.d 0 4) (by simp) with h68 | h68
                                      · linarith only [h6, h68, hlam]
                                      · linarith only [h36, h68, hlam]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h36, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h42, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h46, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [h47, hlam, p48_0]
                                    · have p48_0 := h48c.1
                                      have p48_1 := h48c.2.1
                                      have p48_2 := h48c.2.2.1
                                      have p48_3 := h48c.2.2.2
                                      linarith only [hlam, p48_0]
                                  · linarith only [h47, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h43, h45, h46, hc35, hlam, hphi, u5elo4]
                              · linarith only [h45, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h42, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h39, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h37, h38, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h3, h37, hc12, hlam, hphi, u2elo0]
                · linarith only [h36, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h85 | h85
            · rcases m.htr 0 3 4 (by decide) (by decide) with h86 | h86
              · linarith only [h3, h4, h86, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h88 | h88
                · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h4, h90, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                        · linarith only [h0, h4, h86, h89, h93, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                            · linarith only [h3, h4, h93, h96, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                              · linarith only [h3, h4, h98, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                              · linarith only [h98, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h90, h95, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h89, h92, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h3, h4, h89, hc12, hlam, hphi, u2elo3]
                · linarith only [h4, h88, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h3, h85, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
            · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                  · linarith only [h106, h110, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                                · linarith only [h0, h112, h118, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h116, h118, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h112, h116, h117, h3, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h0, h108, h112, h116, h3, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h114, h115, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h108, h110, h112, h114, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h112, h113, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h106, h112, h3, hc12, hlam, hphi, u2elo2]
                · linarith only [h109, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h106, h108, h3, hlam]
            · linarith only [h107, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h130 | h130
            · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
              · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                  · linarith only [h0, h133, h3, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
                    · linarith only [h0, h106, h135, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                                  · rcases h4bigk with h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c | h144c
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h135, h137, h141, h143, hc04, hc45, hlam, hphi, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h106, hlam, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h131, h143, hc03, hc45, hlam, hphi, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h106, h140, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h1, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h135, hlam, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h143, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h1, h106, h140, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h140, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo2]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h140, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p144_1, u2elo2]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h140, h143, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h140, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p144_1, u2elo2]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h131, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h138, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h140, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h138, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p144_1]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h132, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h139, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h142, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [h143, hlam, p144_0]
                                    · have p144_0 := h144c.1
                                      have p144_1 := h144c.2.1
                                      have p144_2 := h144c.2.2.1
                                      have p144_3 := h144c.2.2.2
                                      linarith only [hlam, p144_0]
                                  · linarith only [h143, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h142, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h141, h3, hc03, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h131, h140, h3, hlam]
                          · linarith only [h139, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h131, h133, h138, h3, hc12, hlam, hphi, u2elo2]
                      · linarith only [h137, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h132, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                  · linarith only [h179, h3, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                    · linarith only [h0, h106, h131, h181, h3, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                        · linarith only [h0, h131, h179, h183, h184, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                            · linarith only [h0, h131, h183, h187, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h190 | h190
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                                  · rcases h4bigk with h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h106, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p192_1, u2elo3]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h106, hlam, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h131, hlam, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h106, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p192_1, u2elo3]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h1, hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h181, hlam, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h184, hlam, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p192_1, u2elo3]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p192_1, u2elo3]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h187, hlam, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p192_1, u2elo3]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h1, h179, h183, h184, h189, h191, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h179, h183, h184, h189, h191, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h0, h106, h183, h189, h191, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p192_1]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      rcases p192_3 (m.d 0 4) (by simp) with h212 | h212
                                      · linarith only [h131, h212, hlam]
                                      · linarith only [h178, h212, hlam]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h178, hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h186, hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h190, hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [h191, hlam, p192_0]
                                    · have p192_0 := h192c.1
                                      have p192_1 := h192c.2.1
                                      have p192_2 := h192c.2.2.1
                                      have p192_3 := h192c.2.2.2
                                      linarith only [hlam, p192_0]
                                  · linarith only [h191, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h1, h183, h186, h187, h190, h3, hc04, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h183, h189, h3, hc25, hlam, hphi, u5elo3]
                          · linarith only [h186, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h183, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h178, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h130, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h228 | h228
      · rcases m.htr 0 2 3 (by decide) (by decide) with h229 | h229
        · rcases m.htr 0 2 4 (by decide) (by decide) with h230 | h230
          · linarith only [h0, h1, h230, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
            · rcases m.htr 0 3 4 (by decide) (by decide) with h233 | h233
              · linarith only [h0, h1, h229, h233, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h235 | h235
                · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                    · linarith only [h0, h1, h230, h237, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h236, h237, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1, h229, h230, h236, hc12, hlam, hphi, u2elo3]
                · linarith only [h1, h235, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h232, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h243 | h243
          · linarith only [h0, h1, h229, h243, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
            · rcases m.htr 0 3 4 (by decide) (by decide) with h246 | h246
              · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
                · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                  · linarith only [h0, h1, h229, h248, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                    · linarith only [h0, h1, h243, h250, hlam]
                    · linarith only [h0, h1, h250, hc12, hlam, hphi, u2elo3]
                · linarith only [h0, h1, h247, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h254 | h254
                · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                  · linarith only [h0, h1, h229, h255, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
                    · linarith only [h0, h1, h243, h257, hlam]
                    · linarith only [h0, h1, h257, hc12, hlam, hphi, u2elo3]
                · linarith only [h246, h254, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h245, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h228, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h263 | h263
    · rcases m.htr 0 1 5 (by decide) (by decide) with h264 | h264
      · rcases m.htr 0 2 3 (by decide) (by decide) with h265 | h265
        · rcases m.htr 0 2 4 (by decide) (by decide) with h266 | h266
          · rcases m.htr 0 2 5 (by decide) (by decide) with h267 | h267
            · rcases m.htr 0 3 4 (by decide) (by decide) with h268 | h268
              · rcases m.htr 0 4 5 (by decide) (by decide) with h269 | h269
                · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                          · linarith only [h0, h263, h274, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h274, hc14, hlam, hphi, ht45, u5elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                          · linarith only [h0, h263, h277, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h277, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h272, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h263, h269, h271, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h263, h269, h270, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h269, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h284 | h284
                · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                        · linarith only [h0, h263, h265, h268, h288, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                          · linarith only [h0, h263, h290, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h290, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h287, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h286, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h263, h285, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h268, h284, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h263, h267, hc14, hlam, hphi, ht45, u5elo2]
          · linarith only [h0, h263, h266, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h299 | h299
          · rcases m.htr 0 2 5 (by decide) (by decide) with h300 | h300
            · rcases m.htr 0 3 4 (by decide) (by decide) with h301 | h301
              · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
                · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                  · linarith only [h0, h263, h265, h303, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h263, h303, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h302, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h0, h263, h265, h301, hlam]
            · linarith only [h0, h263, h300, hc14, hlam, hphi, ht45, u5elo2]
          · linarith only [h0, h263, h299, hlam]
      · linarith only [h263, h264, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h311 | h311
      · rcases m.htr 0 2 3 (by decide) (by decide) with h312 | h312
        · rcases m.htr 0 2 4 (by decide) (by decide) with h313 | h313
          · rcases m.htr 0 2 5 (by decide) (by decide) with h314 | h314
            · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
              · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
                                  · linarith only [h312, h322, h325, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h325, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h321, h324, hc24, hlam, hphi, ht45, u5elo1]
                              · linarith only [h323, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                              · linarith only [h0, h312, h315, h322, h330, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h330, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h263, h321, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h263, h311, h312, h315, h319, h320, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h319, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h311, h313, h318, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h312, h317, hlam]
                · linarith only [h263, h311, h316, hc15, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h344 | h344
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                            · linarith only [h312, h315, h345, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                              · linarith only [h312, h315, h340, h343, h347, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h347, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h263, h311, h342, h344, hc25, hlam, hphi, u5elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h351 | h351
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                            · linarith only [h312, h315, h352, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                                  · rcases h4bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h263, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h0, h313, h352, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p357_1, u2elo1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h315, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h0, h313, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p357_1, u2elo1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h263, h311, h342, h354, h356, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h341, h352, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p357_1, u2elo1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h343, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h341, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p357_1, u2elo1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h313, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h341, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h352, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p357_1, u2elo3]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h263, h311, h342, h354, h356, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h263, h311, h342, h354, h356, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h352, h354, h356, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      rcases p357_3 (m.d 0 4) (by simp) with h377 | h377
                                      · linarith only [h315, h377, hlam]
                                      · linarith only [h339, h377, hlam]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h339, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h351, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h355, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h356, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                  · linarith only [h356, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h263, h311, h341, h351, h352, h355, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h354, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h263, h351, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h263, h311, h341, h342, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                    · linarith only [h0, h311, h341, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h311, h312, h340, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h263, h311, h339, hc15, hlam, hphi, u5elo4]
            · linarith only [h314, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
            · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
              · linarith only [h312, h313, h395, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
                · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                    · linarith only [h312, h313, h399, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h311, h399, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h311, h312, h398, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h397, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h394, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h405 | h405
          · rcases m.htr 0 2 5 (by decide) (by decide) with h406 | h406
            · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
              · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
                · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                  · linarith only [h263, h311, h312, h405, h409, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h311, h409, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h263, h311, h408, hc15, hlam, hphi, u5elo4]
              · linarith only [h312, h405, h407, hlam]
            · linarith only [h263, h311, h405, h406, hc15, hlam, hphi, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h415 | h415
            · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
              · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
                · rcases m.htr 1 2 3 (by decide) (by decide) with h418 | h418
                  · linarith only [h312, h418, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h311, h418, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h311, h405, h417, hc15, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h422 | h422
                · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                  · linarith only [h0, h311, h312, h423, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h311, h423, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h416, h422, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h311, h415, hc15, hlam, hphi, u5elo2]
      · linarith only [h311, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem n7l_sAB2_H_I_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h15 | h15
    · rcases p0_3 (m.d 1 4) (by simp) with h16 | h16
      · rcases p0_3 (m.d 2 4) (by simp) with h17 | h17
        · linarith only [h17, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 4 5) (by simp) with h20 | h20
            · linarith only [h20, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h20, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h23 | h23
            · linarith only [h23, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h23, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h16, h29, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h16, h32, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h32, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
    · rcases p0_3 (m.d 1 4) (by simp) with h37 | h37
      · rcases p0_3 (m.d 2 4) (by simp) with h38 | h38
        · linarith only [h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h40 | h40
          · linarith only [h40, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h42, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h42, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h45 | h45
        · linarith only [h37, h45, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h47 | h47
          · linarith only [h47, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · linarith only [h37, h49, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h49, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h54 | h54
    · linarith only [h54, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h56 | h56
      · rcases p0_3 (m.d 2 4) (by simp) with h57 | h57
        · linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h56, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · rcases p0_3 (m.d 2 4) (by simp) with h70 | h70
        · linarith only [h70, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · rcases p0_3 (m.d 2 4) (by simp) with h81 | h81
        · linarith only [h81, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h84, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h68, h87, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h87, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h80, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h95 | h95
          · linarith only [h95, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h97 | h97
            · linarith only [h97, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h91, h97, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h92, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · rcases p0_3 (m.d 2 4) (by simp) with h102 | h102
        · linarith only [h102, h91, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · linarith only [h104, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, h91, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h106, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h101, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
    · linarith only [h116, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h118 | h118
      · rcases p0_3 (m.d 2 4) (by simp) with h119 | h119
        · linarith only [h119, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, h122, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · linarith only [h126, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h128, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · linarith only [h136, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h133, h139, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h143 | h143
      · linarith only [h143, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h145 | h145
        · linarith only [h133, h145, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 4 5) (by simp) with h148 | h148
            · linarith only [h133, h148, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h147, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
    · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
      · rcases p0_3 (m.d 2 4) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 4 5) (by simp) with h157 | h157
            · linarith only [h157, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h152, h157, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h161 | h161
        · linarith only [h161, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h153, h164, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h164, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
      · rcases p0_3 (m.d 2 4) (by simp) with h169 | h169
        · linarith only [h169, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 4 5) (by simp) with h172 | h172
            · linarith only [h152, h172, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h168, h172, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h176 | h176
        · linarith only [h176, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h178 | h178
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h152, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h178, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h5, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h16 | h16
    · rcases p0_3 (m.d 1 4) (by simp) with h17 | h17
      · rcases p0_3 (m.d 2 4) (by simp) with h18 | h18
        · rcases p0_3 (m.d 3 4) (by simp) with h19 | h19
          · linarith only [h19, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h21, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h17, h18, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h25 | h25
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · linarith only [h26, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h28 | h28
            · linarith only [h17, h28, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h28, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h25, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
    · linarith only [h16, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · linarith only [h34, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · rcases p0_3 (m.d 4 5) (by simp) with h39 | h39
            · linarith only [h39, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h39, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h42, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h42, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h37, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h49 | h49
    · rcases p0_3 (m.d 1 4) (by simp) with h50 | h50
      · rcases p0_3 (m.d 2 4) (by simp) with h51 | h51
        · rcases p0_3 (m.d 3 4) (by simp) with h52 | h52
          · linarith only [h52, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h54 | h54
            · linarith only [h54, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h49, h54, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h51, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h50, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h59 | h59
      · rcases p0_3 (m.d 2 4) (by simp) with h60 | h60
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h49, h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h69 | h69
    · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · rcases p0_3 (m.d 3 4) (by simp) with h73 | h73
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · linarith only [h74, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h74, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h77 | h77
            · linarith only [h77, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h72, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h81 | h81
        · rcases p0_3 (m.d 3 4) (by simp) with h82 | h82
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h86, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h86, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h81, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · rcases p0_3 (m.d 1 4) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · linarith only [h95, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h90, h95, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h98, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h106, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h109 | h109
            · linarith only [h109, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h109, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h123, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h130 | h130
      · rcases p0_3 (m.d 2 4) (by simp) with h131 | h131
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h114, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h130, h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h131, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h138 | h138
        · rcases p0_3 (m.d 3 4) (by simp) with h139 | h139
          · linarith only [h139, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h141 | h141
            · linarith only [h114, h141, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h141, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h138, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
    · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h148 | h148
      · rcases p0_3 (m.d 2 4) (by simp) with h149 | h149
        · rcases p0_3 (m.d 3 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 4 5) (by simp) with h151 | h151
            · linarith only [h151, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, h151, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h150, hlam, p0_0]
        · linarith only [h149, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h156 | h156
        · rcases p0_3 (m.d 3 4) (by simp) with h157 | h157
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, h158, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h157, hlam, p0_0]
        · linarith only [h156, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h164, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h163, h168, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h167, hlam, p0_0]
        · linarith only [h166, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h173 | h173
      · linarith only [h173, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h175 | h175
        · rcases p0_3 (m.d 3 4) (by simp) with h176 | h176
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · linarith only [h163, h177, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h175, h177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h176, hlam, p0_0]
        · linarith only [h175, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h2elo := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases h5bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc15, hlam, hphi, p10_1, u5elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc25, hlam, hphi, p10_1, u5elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc35, hlam, hphi, p10_1, u5elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc45, hlam, hphi, p10_1, u5elo0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc05, hlam, hphi, p10_1, u5elo1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc25, hlam, hphi, p10_1, u5elo1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc35, hlam, hphi, p10_1, u5elo1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc45, hlam, hphi, p10_1, u5elo1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc05, hlam, hphi, p10_1, u5elo2]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc15, hlam, hphi, p10_1, u5elo2]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc35, hlam, hphi, p10_1, u5elo2]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc45, hlam, hphi, p10_1, u5elo2]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc05, hlam, hphi, p10_1, u5elo3]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc15, hlam, hphi, p10_1, u5elo3]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc25, hlam, hphi, p10_1, u5elo3]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc45, hlam, hphi, p10_1, u5elo3]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hc05, hlam, hphi, p10_1, u5elo4]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h8, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h7, h8, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [h7, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p10_1]
              · have p10_0 := h10c.1
                have p10_1 := h10c.2.1
                have p10_2 := h10c.2.2.1
                have p10_3 := h10c.2.2.2
                linarith only [hlam, p10_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h36 | h36
            · linarith only [h36, hc14, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc15, hlam, hphi, p38_1, u5elo0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc25, hlam, hphi, p38_1, u5elo0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc35, hlam, hphi, p38_1, u5elo0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc45, hlam, hphi, p38_1, u5elo0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc05, hlam, hphi, p38_1, u5elo1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc25, hlam, hphi, p38_1, u5elo1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc35, hlam, hphi, p38_1, u5elo1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc45, hlam, hphi, p38_1, u5elo1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc05, hlam, hphi, p38_1, u5elo2]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc15, hlam, hphi, p38_1, u5elo2]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc35, hlam, hphi, p38_1, u5elo2]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc45, hlam, hphi, p38_1, u5elo2]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc05, hlam, hphi, p38_1, u5elo3]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc15, hlam, hphi, p38_1, u5elo3]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc25, hlam, hphi, p38_1, u5elo3]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc45, hlam, hphi, p38_1, u5elo3]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hc05, hlam, hphi, p38_1, u5elo4]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h36, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h36, hc04, hc25, hlam, hphi, ht0b, ht5b, p0_1, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [h36, hc04, hc35, hlam, hphi, ht0b, ht5b, p0_1, p38_1]
              · have p38_0 := h38c.1
                have p38_1 := h38c.2.1
                have p38_2 := h38c.2.2.1
                have p38_3 := h38c.2.2.2
                linarith only [hlam, p38_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
    · rcases p0_3 (m.d 1 4) (by simp) with h66 | h66
      · rcases p0_3 (m.d 2 4) (by simp) with h67 | h67
        · linarith only [h67, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h69 | h69
          · rcases p0_3 (m.d 4 5) (by simp) with h70 | h70
            · linarith only [h70, hc24, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hlam, p72_0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc15, hlam, hphi, p72_1, u5elo0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc25, hlam, hphi, p72_1, u5elo0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc35, hlam, hphi, p72_1, u5elo0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc45, hlam, hphi, p72_1, u5elo0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc05, hlam, hphi, p72_1, u5elo1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hlam, p72_0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc25, hlam, hphi, p72_1, u5elo1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc35, hlam, hphi, p72_1, u5elo1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc45, hlam, hphi, p72_1, u5elo1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc05, hlam, hphi, p72_1, u5elo2]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc15, hlam, hphi, p72_1, u5elo2]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hlam, p72_0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc35, hlam, hphi, p72_1, u5elo2]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc45, hlam, hphi, p72_1, u5elo2]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc05, hlam, hphi, p72_1, u5elo3]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc15, hlam, hphi, p72_1, u5elo3]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc25, hlam, hphi, p72_1, u5elo3]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hlam, p72_0]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc45, hlam, hphi, p72_1, u5elo3]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hc05, hlam, hphi, p72_1, u5elo4]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [h70, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p72_1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [h69, h70, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p72_1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [h69, h70, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p72_1]
              · have p72_0 := h72c.1
                have p72_1 := h72c.2.1
                have p72_2 := h72c.2.2.1
                have p72_3 := h72c.2.2.2
                linarith only [hlam, p72_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc24, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hlam, p100_0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc15, hlam, hphi, p100_1, u5elo0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc25, hlam, hphi, p100_1, u5elo0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc35, hlam, hphi, p100_1, u5elo0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc45, hlam, hphi, p100_1, u5elo0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc05, hlam, hphi, p100_1, u5elo1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hlam, p100_0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc25, hlam, hphi, p100_1, u5elo1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc35, hlam, hphi, p100_1, u5elo1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc45, hlam, hphi, p100_1, u5elo1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc05, hlam, hphi, p100_1, u5elo2]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc15, hlam, hphi, p100_1, u5elo2]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hlam, p100_0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc35, hlam, hphi, p100_1, u5elo2]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc45, hlam, hphi, p100_1, u5elo2]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc05, hlam, hphi, p100_1, u5elo3]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc15, hlam, hphi, p100_1, u5elo3]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc25, hlam, hphi, p100_1, u5elo3]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hlam, p100_0]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc45, hlam, hphi, p100_1, u5elo3]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hc05, hlam, hphi, p100_1, u5elo4]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [h98, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p100_1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [h66, h98, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p100_1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [h66, h98, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p100_1]
              · have p100_0 := h100c.1
                have p100_1 := h100c.2.1
                have p100_2 := h100c.2.2.1
                have p100_3 := h100c.2.2.2
                linarith only [hlam, p100_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · linarith only [h126, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, h66, hc14, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hlam, p131_0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc15, hlam, hphi, p131_1, u5elo0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc25, hlam, hphi, p131_1, u5elo0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc35, hlam, hphi, p131_1, u5elo0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc45, hlam, hphi, p131_1, u5elo0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc05, hlam, hphi, p131_1, u5elo1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hlam, p131_0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc25, hlam, hphi, p131_1, u5elo1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc35, hlam, hphi, p131_1, u5elo1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc45, hlam, hphi, p131_1, u5elo1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc05, hlam, hphi, p131_1, u5elo2]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc15, hlam, hphi, p131_1, u5elo2]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hlam, p131_0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc35, hlam, hphi, p131_1, u5elo2]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc45, hlam, hphi, p131_1, u5elo2]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc05, hlam, hphi, p131_1, u5elo3]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc15, hlam, hphi, p131_1, u5elo3]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc25, hlam, hphi, p131_1, u5elo3]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hlam, p131_0]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc45, hlam, hphi, p131_1, u5elo3]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hc05, hlam, hphi, p131_1, u5elo4]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [h129, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p131_1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [h128, h129, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p131_1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [h128, h129, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p131_1]
              · have p131_0 := h131c.1
                have p131_1 := h131c.2.1
                have p131_2 := h131c.2.2.1
                have p131_3 := h131c.2.2.2
                linarith only [hlam, p131_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h157 | h157
            · linarith only [h157, h66, hc14, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hlam, p159_0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc15, hlam, hphi, p159_1, u5elo0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc25, hlam, hphi, p159_1, u5elo0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc35, hlam, hphi, p159_1, u5elo0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc45, hlam, hphi, p159_1, u5elo0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc05, hlam, hphi, p159_1, u5elo1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hlam, p159_0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc25, hlam, hphi, p159_1, u5elo1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc35, hlam, hphi, p159_1, u5elo1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc45, hlam, hphi, p159_1, u5elo1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc05, hlam, hphi, p159_1, u5elo2]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc15, hlam, hphi, p159_1, u5elo2]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hlam, p159_0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc35, hlam, hphi, p159_1, u5elo2]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc45, hlam, hphi, p159_1, u5elo2]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc05, hlam, hphi, p159_1, u5elo3]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc15, hlam, hphi, p159_1, u5elo3]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc25, hlam, hphi, p159_1, u5elo3]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hlam, p159_0]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc45, hlam, hphi, p159_1, u5elo3]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hc05, hlam, hphi, p159_1, u5elo4]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [h157, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p159_1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [h157, hc04, hc25, hlam, hphi, ht0b, ht5b, p0_1, p159_1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [h157, hc04, hc35, hlam, hphi, ht0b, ht5b, p0_1, p159_1]
              · have p159_0 := h159c.1
                have p159_1 := h159c.2.1
                have p159_2 := h159c.2.2.1
                have p159_3 := h159c.2.2.2
                linarith only [hlam, p159_0]
    · linarith only [h65, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h186 | h186
    · rcases p0_3 (m.d 1 4) (by simp) with h187 | h187
      · rcases p0_3 (m.d 2 4) (by simp) with h188 | h188
        · linarith only [h188, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h190 | h190
          · linarith only [h190, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h192 | h192
            · linarith only [h192, hc34, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hlam, p194_0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc15, hlam, hphi, p194_1, u5elo0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc25, hlam, hphi, p194_1, u5elo0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc35, hlam, hphi, p194_1, u5elo0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc45, hlam, hphi, p194_1, u5elo0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc05, hlam, hphi, p194_1, u5elo1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hlam, p194_0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc25, hlam, hphi, p194_1, u5elo1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc35, hlam, hphi, p194_1, u5elo1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc45, hlam, hphi, p194_1, u5elo1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc05, hlam, hphi, p194_1, u5elo2]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc15, hlam, hphi, p194_1, u5elo2]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hlam, p194_0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc35, hlam, hphi, p194_1, u5elo2]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc45, hlam, hphi, p194_1, u5elo2]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc05, hlam, hphi, p194_1, u5elo3]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc15, hlam, hphi, p194_1, u5elo3]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc25, hlam, hphi, p194_1, u5elo3]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hlam, p194_0]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc45, hlam, hphi, p194_1, u5elo3]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hc05, hlam, hphi, p194_1, u5elo4]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [h192, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p194_1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [h187, h192, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p194_1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [h187, h192, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p194_1]
              · have p194_0 := h194c.1
                have p194_1 := h194c.2.1
                have p194_2 := h194c.2.2.1
                have p194_3 := h194c.2.2.2
                linarith only [hlam, p194_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h220 | h220
        · linarith only [h187, h220, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h222 | h222
          · linarith only [h222, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h224 | h224
            · linarith only [h187, h224, hc14, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hlam, p226_0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc15, hlam, hphi, p226_1, u5elo0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc25, hlam, hphi, p226_1, u5elo0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc35, hlam, hphi, p226_1, u5elo0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc45, hlam, hphi, p226_1, u5elo0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc05, hlam, hphi, p226_1, u5elo1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hlam, p226_0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc25, hlam, hphi, p226_1, u5elo1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc35, hlam, hphi, p226_1, u5elo1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc45, hlam, hphi, p226_1, u5elo1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc05, hlam, hphi, p226_1, u5elo2]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc15, hlam, hphi, p226_1, u5elo2]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hlam, p226_0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc35, hlam, hphi, p226_1, u5elo2]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc45, hlam, hphi, p226_1, u5elo2]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc05, hlam, hphi, p226_1, u5elo3]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc15, hlam, hphi, p226_1, u5elo3]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc25, hlam, hphi, p226_1, u5elo3]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hlam, p226_0]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc45, hlam, hphi, p226_1, u5elo3]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hc05, hlam, hphi, p226_1, u5elo4]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [h224, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p226_1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [h224, hc04, hc25, hlam, hphi, ht0b, ht5b, p0_1, p226_1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [h224, hc04, hc35, hlam, hphi, ht0b, ht5b, p0_1, p226_1]
              · have p226_0 := h226c.1
                have p226_1 := h226c.2.1
                have p226_2 := h226c.2.2.1
                have p226_3 := h226c.2.2.2
                linarith only [hlam, p226_0]
    · linarith only [h186, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h253 | h253
    · rcases p0_3 (m.d 1 4) (by simp) with h254 | h254
      · rcases p0_3 (m.d 2 4) (by simp) with h255 | h255
        · linarith only [h255, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h257 | h257
          · rcases p0_3 (m.d 4 5) (by simp) with h258 | h258
            · linarith only [h258, hlam, p0_0]
            · rcases h5bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hlam, p260_0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc15, hlam, hphi, p260_1, u5elo0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc25, hlam, hphi, p260_1, u5elo0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc35, hlam, hphi, p260_1, u5elo0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h255, hc24, hlam, hphi, ht45, p260_1, u5elo0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc05, hlam, hphi, p260_1, u5elo1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hlam, p260_0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc25, hlam, hphi, p260_1, u5elo1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc35, hlam, hphi, p260_1, u5elo1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h255, hc24, hlam, hphi, ht45, p260_1, u5elo1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc05, hlam, hphi, p260_1, u5elo2]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc15, hlam, hphi, p260_1, u5elo2]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hlam, p260_0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc35, hlam, hphi, p260_1, u5elo2]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h255, hc24, hlam, hphi, ht45, p260_1, u5elo2]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc05, hlam, hphi, p260_1, u5elo3]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc15, hlam, hphi, p260_1, u5elo3]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc25, hlam, hphi, p260_1, u5elo3]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hlam, p260_0]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h255, hc24, hlam, hphi, ht45, p260_1, u5elo3]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hc04, hc05, hlam, hphi, ht0b, ht5b, p0_1, p260_1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h257, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p260_1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h257, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p260_1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [h257, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p260_1]
              · have p260_0 := h260c.1
                have p260_1 := h260c.2.1
                have p260_2 := h260c.2.2.1
                have p260_3 := h260c.2.2.2
                linarith only [hlam, p260_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h286 | h286
            · linarith only [h286, hlam, p0_0]
            · rcases h5bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hlam, p288_0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc15, hlam, hphi, p288_1, u5elo0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc25, hlam, hphi, p288_1, u5elo0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc35, hlam, hphi, p288_1, u5elo0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h257, hc34, hlam, hphi, ht45, p288_1, u5elo0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc05, hlam, hphi, p288_1, u5elo1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hlam, p288_0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc25, hlam, hphi, p288_1, u5elo1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc35, hlam, hphi, p288_1, u5elo1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h257, hc34, hlam, hphi, ht45, p288_1, u5elo1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc05, hlam, hphi, p288_1, u5elo2]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc15, hlam, hphi, p288_1, u5elo2]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hlam, p288_0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc35, hlam, hphi, p288_1, u5elo2]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h257, hc34, hlam, hphi, ht45, p288_1, u5elo2]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc05, hlam, hphi, p288_1, u5elo3]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc15, hlam, hphi, p288_1, u5elo3]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc25, hlam, hphi, p288_1, u5elo3]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hlam, p288_0]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h257, hc34, hlam, hphi, ht45, p288_1, u5elo3]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hc05, hlam, hphi, p288_1, u5elo4]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h254, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p288_1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h254, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p288_1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [h254, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p288_1]
              · have p288_0 := h288c.1
                have p288_1 := h288c.2.1
                have p288_2 := h288c.2.2.1
                have p288_3 := h288c.2.2.2
                linarith only [hlam, p288_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h314 | h314
        · linarith only [h254, h314, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h316 | h316
          · rcases p0_3 (m.d 4 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases h5bigk with h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hlam, p319_0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc15, hlam, hphi, p319_1, u5elo0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc25, hlam, hphi, p319_1, u5elo0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc35, hlam, hphi, p319_1, u5elo0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p319_1, u5elo0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc05, hlam, hphi, p319_1, u5elo1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hlam, p319_0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc25, hlam, hphi, p319_1, u5elo1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc35, hlam, hphi, p319_1, u5elo1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p319_1, u5elo1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc05, hlam, hphi, p319_1, u5elo2]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc15, hlam, hphi, p319_1, u5elo2]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hlam, p319_0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc35, hlam, hphi, p319_1, u5elo2]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p319_1, u5elo2]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc05, hlam, hphi, p319_1, u5elo3]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc15, hlam, hphi, p319_1, u5elo3]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc25, hlam, hphi, p319_1, u5elo3]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hlam, p319_0]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p319_1, u5elo3]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hc04, hc05, hlam, hphi, ht0b, ht5b, p0_1, p319_1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h316, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p319_1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h316, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p319_1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [h316, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p319_1]
              · have p319_0 := h319c.1
                have p319_1 := h319c.2.1
                have p319_2 := h319c.2.2.1
                have p319_3 := h319c.2.2.2
                linarith only [hlam, p319_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h345 | h345
            · linarith only [h345, hlam, p0_0]
            · rcases h5bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc15, hlam, hphi, p347_1, u5elo0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc25, hlam, hphi, p347_1, u5elo0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc35, hlam, hphi, p347_1, u5elo0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p347_1, u5elo0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc05, hlam, hphi, p347_1, u5elo1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc25, hlam, hphi, p347_1, u5elo1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc35, hlam, hphi, p347_1, u5elo1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p347_1, u5elo1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc05, hlam, hphi, p347_1, u5elo2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc15, hlam, hphi, p347_1, u5elo2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc35, hlam, hphi, p347_1, u5elo2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p347_1, u5elo2]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc05, hlam, hphi, p347_1, u5elo3]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc15, hlam, hphi, p347_1, u5elo3]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc25, hlam, hphi, p347_1, u5elo3]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [h254, hc14, hlam, hphi, ht45, p347_1, u5elo3]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc04, hc05, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc04, hc25, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hc04, hc35, hlam, hphi, ht0b, ht5b, p0_1, p347_1]
              · have p347_0 := h347c.1
                have p347_1 := h347c.2.1
                have p347_2 := h347c.2.2.1
                have p347_3 := h347c.2.2.2
                linarith only [hlam, p347_0]
    · linarith only [h253, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h374 | h374
    · linarith only [h374, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h376 | h376
      · rcases p0_3 (m.d 2 4) (by simp) with h377 | h377
        · linarith only [h377, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h379 | h379
          · rcases p0_3 (m.d 4 5) (by simp) with h380 | h380
            · linarith only [h380, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc15, hlam, hphi, p382_1, u5elo0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc25, hlam, hphi, p382_1, u5elo0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc35, hlam, hphi, p382_1, u5elo0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc45, hlam, hphi, p382_1, u5elo0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc05, hlam, hphi, p382_1, u5elo1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc25, hlam, hphi, p382_1, u5elo1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc35, hlam, hphi, p382_1, u5elo1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc45, hlam, hphi, p382_1, u5elo1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc05, hlam, hphi, p382_1, u5elo2]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc15, hlam, hphi, p382_1, u5elo2]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc35, hlam, hphi, p382_1, u5elo2]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc45, hlam, hphi, p382_1, u5elo2]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc05, hlam, hphi, p382_1, u5elo3]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc15, hlam, hphi, p382_1, u5elo3]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc25, hlam, hphi, p382_1, u5elo3]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc45, hlam, hphi, p382_1, u5elo3]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hc05, hlam, hphi, p382_1, u5elo4]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h380, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h379, h380, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [h379, h380, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p382_1]
              · have p382_0 := h382c.1
                have p382_1 := h382c.2.1
                have p382_2 := h382c.2.2.1
                have p382_3 := h382c.2.2.2
                linarith only [hlam, p382_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h408 | h408
            · linarith only [h408, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc15, hlam, hphi, p410_1, u5elo0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc25, hlam, hphi, p410_1, u5elo0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc35, hlam, hphi, p410_1, u5elo0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc45, hlam, hphi, p410_1, u5elo0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc05, hlam, hphi, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc25, hlam, hphi, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc35, hlam, hphi, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc45, hlam, hphi, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc05, hlam, hphi, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc15, hlam, hphi, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc35, hlam, hphi, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc45, hlam, hphi, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc05, hlam, hphi, p410_1, u5elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc15, hlam, hphi, p410_1, u5elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc25, hlam, hphi, p410_1, u5elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc45, hlam, hphi, p410_1, u5elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc05, hlam, hphi, p410_1, u5elo4]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h408, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h408, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h408, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
      · linarith only [h376, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h438 | h438
    · rcases p0_3 (m.d 1 4) (by simp) with h439 | h439
      · rcases p0_3 (m.d 2 4) (by simp) with h440 | h440
        · linarith only [h440, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h442 | h442
          · rcases p0_3 (m.d 4 5) (by simp) with h443 | h443
            · linarith only [h443, hc24, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hlam, p445_0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc15, hlam, hphi, p445_1, u5elo0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc25, hlam, hphi, p445_1, u5elo0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc35, hlam, hphi, p445_1, u5elo0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc45, hlam, hphi, p445_1, u5elo0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc05, hlam, hphi, p445_1, u5elo1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hlam, p445_0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc25, hlam, hphi, p445_1, u5elo1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc35, hlam, hphi, p445_1, u5elo1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc45, hlam, hphi, p445_1, u5elo1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc05, hlam, hphi, p445_1, u5elo2]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc15, hlam, hphi, p445_1, u5elo2]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hlam, p445_0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc35, hlam, hphi, p445_1, u5elo2]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc45, hlam, hphi, p445_1, u5elo2]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc05, hlam, hphi, p445_1, u5elo3]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc15, hlam, hphi, p445_1, u5elo3]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc25, hlam, hphi, p445_1, u5elo3]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hlam, p445_0]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc45, hlam, hphi, p445_1, u5elo3]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hc05, hlam, hphi, p445_1, u5elo4]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [h438, h443, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p445_1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [h442, h443, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p445_1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [h442, h443, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p445_1]
              · have p445_0 := h445c.1
                have p445_1 := h445c.2.1
                have p445_2 := h445c.2.2.1
                have p445_3 := h445c.2.2.2
                linarith only [hlam, p445_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h471 | h471
            · linarith only [h471, hc24, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hlam, p473_0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc15, hlam, hphi, p473_1, u5elo0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc25, hlam, hphi, p473_1, u5elo0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc35, hlam, hphi, p473_1, u5elo0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc45, hlam, hphi, p473_1, u5elo0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc05, hlam, hphi, p473_1, u5elo1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hlam, p473_0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc25, hlam, hphi, p473_1, u5elo1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc35, hlam, hphi, p473_1, u5elo1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc45, hlam, hphi, p473_1, u5elo1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc05, hlam, hphi, p473_1, u5elo2]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc15, hlam, hphi, p473_1, u5elo2]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hlam, p473_0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc35, hlam, hphi, p473_1, u5elo2]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc45, hlam, hphi, p473_1, u5elo2]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc05, hlam, hphi, p473_1, u5elo3]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc15, hlam, hphi, p473_1, u5elo3]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc25, hlam, hphi, p473_1, u5elo3]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hlam, p473_0]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc45, hlam, hphi, p473_1, u5elo3]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hc05, hlam, hphi, p473_1, u5elo4]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [h471, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p473_1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [h471, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p473_1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [h471, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p473_1]
              · have p473_0 := h473c.1
                have p473_1 := h473c.2.1
                have p473_2 := h473c.2.2.1
                have p473_3 := h473c.2.2.2
                linarith only [hlam, p473_0]
      · linarith only [h439, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h500 | h500
      · rcases p0_3 (m.d 2 4) (by simp) with h501 | h501
        · linarith only [h501, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h503 | h503
          · rcases p0_3 (m.d 4 5) (by simp) with h504 | h504
            · linarith only [h438, h504, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hlam, p506_0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc15, hlam, hphi, p506_1, u5elo0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc25, hlam, hphi, p506_1, u5elo0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc35, hlam, hphi, p506_1, u5elo0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc45, hlam, hphi, p506_1, u5elo0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc05, hlam, hphi, p506_1, u5elo1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hlam, p506_0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc25, hlam, hphi, p506_1, u5elo1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc35, hlam, hphi, p506_1, u5elo1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc45, hlam, hphi, p506_1, u5elo1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc05, hlam, hphi, p506_1, u5elo2]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc15, hlam, hphi, p506_1, u5elo2]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hlam, p506_0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc35, hlam, hphi, p506_1, u5elo2]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc45, hlam, hphi, p506_1, u5elo2]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc05, hlam, hphi, p506_1, u5elo3]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc15, hlam, hphi, p506_1, u5elo3]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc25, hlam, hphi, p506_1, u5elo3]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hlam, p506_0]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc45, hlam, hphi, p506_1, u5elo3]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hc05, hlam, hphi, p506_1, u5elo4]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [h504, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p506_1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [h503, h504, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p506_1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [h503, h504, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p506_1]
              · have p506_0 := h506c.1
                have p506_1 := h506c.2.1
                have p506_2 := h506c.2.2.1
                have p506_3 := h506c.2.2.2
                linarith only [hlam, p506_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h532 | h532
            · linarith only [h438, h532, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c | h534c
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hlam, p534_0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc15, hlam, hphi, p534_1, u5elo0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc25, hlam, hphi, p534_1, u5elo0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc35, hlam, hphi, p534_1, u5elo0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc45, hlam, hphi, p534_1, u5elo0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc05, hlam, hphi, p534_1, u5elo1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hlam, p534_0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc25, hlam, hphi, p534_1, u5elo1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc35, hlam, hphi, p534_1, u5elo1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc45, hlam, hphi, p534_1, u5elo1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc05, hlam, hphi, p534_1, u5elo2]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc15, hlam, hphi, p534_1, u5elo2]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hlam, p534_0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc35, hlam, hphi, p534_1, u5elo2]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc45, hlam, hphi, p534_1, u5elo2]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc05, hlam, hphi, p534_1, u5elo3]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc15, hlam, hphi, p534_1, u5elo3]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc25, hlam, hphi, p534_1, u5elo3]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hlam, p534_0]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc45, hlam, hphi, p534_1, u5elo3]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hc05, hlam, hphi, p534_1, u5elo4]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [h532, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p534_1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [h532, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p534_1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [h532, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p534_1]
              · have p534_0 := h534c.1
                have p534_1 := h534c.2.1
                have p534_2 := h534c.2.2.1
                have p534_3 := h534c.2.2.2
                linarith only [hlam, p534_0]
      · linarith only [h500, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h561 | h561
    · rcases p0_3 (m.d 1 4) (by simp) with h562 | h562
      · rcases p0_3 (m.d 2 4) (by simp) with h563 | h563
        · linarith only [h563, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h565 | h565
          · linarith only [h565, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h567 | h567
            · linarith only [h567, hc34, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hlam, p569_0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc15, hlam, hphi, p569_1, u5elo0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc25, hlam, hphi, p569_1, u5elo0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc35, hlam, hphi, p569_1, u5elo0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc45, hlam, hphi, p569_1, u5elo0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc05, hlam, hphi, p569_1, u5elo1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hlam, p569_0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc25, hlam, hphi, p569_1, u5elo1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc35, hlam, hphi, p569_1, u5elo1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc45, hlam, hphi, p569_1, u5elo1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc05, hlam, hphi, p569_1, u5elo2]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc15, hlam, hphi, p569_1, u5elo2]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hlam, p569_0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc35, hlam, hphi, p569_1, u5elo2]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc45, hlam, hphi, p569_1, u5elo2]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc05, hlam, hphi, p569_1, u5elo3]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc15, hlam, hphi, p569_1, u5elo3]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc25, hlam, hphi, p569_1, u5elo3]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hlam, p569_0]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc45, hlam, hphi, p569_1, u5elo3]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hc05, hlam, hphi, p569_1, u5elo4]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [h561, h567, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p569_1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [h567, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p569_1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [h567, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p569_1]
              · have p569_0 := h569c.1
                have p569_1 := h569c.2.1
                have p569_2 := h569c.2.2.1
                have p569_3 := h569c.2.2.2
                linarith only [hlam, p569_0]
      · linarith only [h562, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h596 | h596
      · rcases p0_3 (m.d 2 4) (by simp) with h597 | h597
        · linarith only [h561, h597, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h599 | h599
          · linarith only [h599, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h601 | h601
            · linarith only [h561, h601, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc15, hlam, hphi, p603_1, u5elo0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc25, hlam, hphi, p603_1, u5elo0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc35, hlam, hphi, p603_1, u5elo0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc45, hlam, hphi, p603_1, u5elo0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc05, hlam, hphi, p603_1, u5elo1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc25, hlam, hphi, p603_1, u5elo1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc35, hlam, hphi, p603_1, u5elo1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc45, hlam, hphi, p603_1, u5elo1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc05, hlam, hphi, p603_1, u5elo2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc15, hlam, hphi, p603_1, u5elo2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc35, hlam, hphi, p603_1, u5elo2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc45, hlam, hphi, p603_1, u5elo2]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc05, hlam, hphi, p603_1, u5elo3]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc15, hlam, hphi, p603_1, u5elo3]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc25, hlam, hphi, p603_1, u5elo3]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc45, hlam, hphi, p603_1, u5elo3]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hc05, hlam, hphi, p603_1, u5elo4]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h601, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h601, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [h601, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p603_1]
              · have p603_0 := h603c.1
                have p603_1 := h603c.2.1
                have p603_2 := h603c.2.2.1
                have p603_3 := h603c.2.2.2
                linarith only [hlam, p603_0]
      · linarith only [h596, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h630 | h630
    · rcases p0_3 (m.d 1 4) (by simp) with h631 | h631
      · rcases p0_3 (m.d 2 4) (by simp) with h632 | h632
        · linarith only [h632, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h634 | h634
          · rcases p0_3 (m.d 4 5) (by simp) with h635 | h635
            · linarith only [h635, hlam, p0_0]
            · rcases h5bigk with h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hlam, p637_0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc15, hlam, hphi, p637_1, u5elo0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc25, hlam, hphi, p637_1, u5elo0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc35, hlam, hphi, p637_1, u5elo0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p637_1, u5elo0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc05, hlam, hphi, p637_1, u5elo1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hlam, p637_0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc25, hlam, hphi, p637_1, u5elo1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc35, hlam, hphi, p637_1, u5elo1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p637_1, u5elo1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc05, hlam, hphi, p637_1, u5elo2]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc15, hlam, hphi, p637_1, u5elo2]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hlam, p637_0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc35, hlam, hphi, p637_1, u5elo2]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p637_1, u5elo2]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc05, hlam, hphi, p637_1, u5elo3]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc15, hlam, hphi, p637_1, u5elo3]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hc25, hlam, hphi, p637_1, u5elo3]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hlam, p637_0]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p637_1, u5elo3]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h630, hc04, hc05, hlam, hphi, ht0b, ht5b, p0_1, p637_1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h634, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p637_1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h634, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p637_1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [h634, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p637_1]
              · have p637_0 := h637c.1
                have p637_1 := h637c.2.1
                have p637_2 := h637c.2.2.1
                have p637_3 := h637c.2.2.2
                linarith only [hlam, p637_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h663 | h663
            · linarith only [h663, hlam, p0_0]
            · rcases h5bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc15, hlam, hphi, p665_1, u5elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc25, hlam, hphi, p665_1, u5elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc35, hlam, hphi, p665_1, u5elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p665_1, u5elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc05, hlam, hphi, p665_1, u5elo1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc25, hlam, hphi, p665_1, u5elo1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc35, hlam, hphi, p665_1, u5elo1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p665_1, u5elo1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc05, hlam, hphi, p665_1, u5elo2]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc15, hlam, hphi, p665_1, u5elo2]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc35, hlam, hphi, p665_1, u5elo2]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p665_1, u5elo2]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc05, hlam, hphi, p665_1, u5elo3]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc15, hlam, hphi, p665_1, u5elo3]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc25, hlam, hphi, p665_1, u5elo3]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h632, hc24, hlam, hphi, ht45, p665_1, u5elo3]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc05, hlam, hphi, p665_1, u5elo4]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
      · linarith only [h631, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h692 | h692
      · rcases p0_3 (m.d 2 4) (by simp) with h693 | h693
        · linarith only [h630, h693, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h695 | h695
          · rcases p0_3 (m.d 4 5) (by simp) with h696 | h696
            · linarith only [h696, hlam, p0_0]
            · rcases h5bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hlam, p698_0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc15, hlam, hphi, p698_1, u5elo0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc25, hlam, hphi, p698_1, u5elo0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc35, hlam, hphi, p698_1, u5elo0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p698_1, u5elo0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc05, hlam, hphi, p698_1, u5elo1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hlam, p698_0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc25, hlam, hphi, p698_1, u5elo1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc35, hlam, hphi, p698_1, u5elo1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p698_1, u5elo1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc05, hlam, hphi, p698_1, u5elo2]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc15, hlam, hphi, p698_1, u5elo2]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hlam, p698_0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc35, hlam, hphi, p698_1, u5elo2]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p698_1, u5elo2]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc05, hlam, hphi, p698_1, u5elo3]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc15, hlam, hphi, p698_1, u5elo3]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc25, hlam, hphi, p698_1, u5elo3]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hlam, p698_0]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p698_1, u5elo3]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, p698_1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h695, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p698_1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h695, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p698_1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [h695, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p698_1]
              · have p698_0 := h698c.1
                have p698_1 := h698c.2.1
                have p698_2 := h698c.2.2.1
                have p698_3 := h698c.2.2.2
                linarith only [hlam, p698_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h724 | h724
            · linarith only [h724, hlam, p0_0]
            · rcases h5bigk with h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc15, hlam, hphi, p726_1, u5elo0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc25, hlam, hphi, p726_1, u5elo0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc35, hlam, hphi, p726_1, u5elo0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p726_1, u5elo0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc05, hlam, hphi, p726_1, u5elo1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc25, hlam, hphi, p726_1, u5elo1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc35, hlam, hphi, p726_1, u5elo1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p726_1, u5elo1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc05, hlam, hphi, p726_1, u5elo2]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc15, hlam, hphi, p726_1, u5elo2]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc35, hlam, hphi, p726_1, u5elo2]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p726_1, u5elo2]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc05, hlam, hphi, p726_1, u5elo3]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc15, hlam, hphi, p726_1, u5elo3]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc25, hlam, hphi, p726_1, u5elo3]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h630, hc04, hlam, hphi, ht45, p726_1, u5elo3]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc05, hlam, hphi, p726_1, u5elo4]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p0_1, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p0_1, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
      · linarith only [h692, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h758 | h758
    · linarith only [h758, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h760 | h760
      · rcases p0_3 (m.d 2 4) (by simp) with h761 | h761
        · linarith only [h761, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h763 | h763
          · rcases p0_3 (m.d 4 5) (by simp) with h764 | h764
            · linarith only [h764, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hlam, p766_0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc15, hlam, hphi, p766_1, u5elo0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc25, hlam, hphi, p766_1, u5elo0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc35, hlam, hphi, p766_1, u5elo0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc45, hlam, hphi, p766_1, u5elo0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc05, hlam, hphi, p766_1, u5elo1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hlam, p766_0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc25, hlam, hphi, p766_1, u5elo1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc35, hlam, hphi, p766_1, u5elo1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc45, hlam, hphi, p766_1, u5elo1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc05, hlam, hphi, p766_1, u5elo2]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc15, hlam, hphi, p766_1, u5elo2]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hlam, p766_0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc35, hlam, hphi, p766_1, u5elo2]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc45, hlam, hphi, p766_1, u5elo2]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc05, hlam, hphi, p766_1, u5elo3]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc15, hlam, hphi, p766_1, u5elo3]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc25, hlam, hphi, p766_1, u5elo3]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hlam, p766_0]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc45, hlam, hphi, p766_1, u5elo3]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hc05, hlam, hphi, p766_1, u5elo4]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [h760, h764, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p766_1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [h764, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p766_1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [h764, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p766_1]
              · have p766_0 := h766c.1
                have p766_1 := h766c.2.1
                have p766_2 := h766c.2.2.1
                have p766_3 := h766c.2.2.2
                linarith only [hlam, p766_0]
          · linarith only [h763, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h793 | h793
        · linarith only [h793, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h795 | h795
          · rcases p0_3 (m.d 4 5) (by simp) with h796 | h796
            · linarith only [h796, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hlam, p798_0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc15, hlam, hphi, p798_1, u5elo0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc25, hlam, hphi, p798_1, u5elo0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc35, hlam, hphi, p798_1, u5elo0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc45, hlam, hphi, p798_1, u5elo0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc05, hlam, hphi, p798_1, u5elo1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hlam, p798_0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc25, hlam, hphi, p798_1, u5elo1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc35, hlam, hphi, p798_1, u5elo1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc45, hlam, hphi, p798_1, u5elo1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc05, hlam, hphi, p798_1, u5elo2]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc15, hlam, hphi, p798_1, u5elo2]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hlam, p798_0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc35, hlam, hphi, p798_1, u5elo2]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc45, hlam, hphi, p798_1, u5elo2]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc05, hlam, hphi, p798_1, u5elo3]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc15, hlam, hphi, p798_1, u5elo3]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc25, hlam, hphi, p798_1, u5elo3]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hlam, p798_0]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc45, hlam, hphi, p798_1, u5elo3]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hc05, hlam, hphi, p798_1, u5elo4]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [h796, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p798_1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [h796, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p798_1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [h796, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p798_1]
              · have p798_0 := h798c.1
                have p798_1 := h798c.2.1
                have p798_2 := h798c.2.2.1
                have p798_3 := h798c.2.2.2
                linarith only [hlam, p798_0]
          · linarith only [h795, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h825 | h825
    · rcases p0_3 (m.d 1 4) (by simp) with h826 | h826
      · linarith only [h826, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h828 | h828
        · linarith only [h828, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h830 | h830
          · rcases p0_3 (m.d 4 5) (by simp) with h831 | h831
            · linarith only [h831, hc14, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hlam, p833_0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc15, hlam, hphi, p833_1, u5elo0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc25, hlam, hphi, p833_1, u5elo0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc35, hlam, hphi, p833_1, u5elo0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc45, hlam, hphi, p833_1, u5elo0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc05, hlam, hphi, p833_1, u5elo1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hlam, p833_0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc25, hlam, hphi, p833_1, u5elo1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc35, hlam, hphi, p833_1, u5elo1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc45, hlam, hphi, p833_1, u5elo1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc05, hlam, hphi, p833_1, u5elo2]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc15, hlam, hphi, p833_1, u5elo2]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hlam, p833_0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc35, hlam, hphi, p833_1, u5elo2]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc45, hlam, hphi, p833_1, u5elo2]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc05, hlam, hphi, p833_1, u5elo3]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc15, hlam, hphi, p833_1, u5elo3]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc25, hlam, hphi, p833_1, u5elo3]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hlam, p833_0]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc45, hlam, hphi, p833_1, u5elo3]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hc05, hlam, hphi, p833_1, u5elo4]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [h825, h831, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p833_1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [h831, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p833_1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [h831, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p833_1]
              · have p833_0 := h833c.1
                have p833_1 := h833c.2.1
                have p833_2 := h833c.2.2.1
                have p833_3 := h833c.2.2.2
                linarith only [hlam, p833_0]
          · linarith only [h830, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h860 | h860
      · linarith only [h860, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h862 | h862
        · linarith only [h825, h862, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h864 | h864
          · rcases p0_3 (m.d 4 5) (by simp) with h865 | h865
            · linarith only [h825, h865, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hlam, p867_0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc15, hlam, hphi, p867_1, u5elo0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc25, hlam, hphi, p867_1, u5elo0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc35, hlam, hphi, p867_1, u5elo0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc45, hlam, hphi, p867_1, u5elo0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc05, hlam, hphi, p867_1, u5elo1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hlam, p867_0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc25, hlam, hphi, p867_1, u5elo1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc35, hlam, hphi, p867_1, u5elo1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc45, hlam, hphi, p867_1, u5elo1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc05, hlam, hphi, p867_1, u5elo2]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc15, hlam, hphi, p867_1, u5elo2]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hlam, p867_0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc35, hlam, hphi, p867_1, u5elo2]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc45, hlam, hphi, p867_1, u5elo2]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc05, hlam, hphi, p867_1, u5elo3]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc15, hlam, hphi, p867_1, u5elo3]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc25, hlam, hphi, p867_1, u5elo3]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hlam, p867_0]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc45, hlam, hphi, p867_1, u5elo3]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hc05, hlam, hphi, p867_1, u5elo4]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [h865, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p867_1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [h865, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p867_1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [h865, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p867_1]
              · have p867_0 := h867c.1
                have p867_1 := h867c.2.1
                have p867_2 := h867c.2.2.1
                have p867_3 := h867c.2.2.2
                linarith only [hlam, p867_0]
          · linarith only [h864, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h894 | h894
    · rcases p0_3 (m.d 1 4) (by simp) with h895 | h895
      · rcases p0_3 (m.d 2 4) (by simp) with h896 | h896
        · linarith only [h896, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h898 | h898
          · rcases p0_3 (m.d 4 5) (by simp) with h899 | h899
            · linarith only [h899, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · rcases h5bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hlam, p901_0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc15, hlam, hphi, p901_1, u5elo0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc25, hlam, hphi, p901_1, u5elo0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc35, hlam, hphi, p901_1, u5elo0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc45, hlam, hphi, p901_1, u5elo0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc05, hlam, hphi, p901_1, u5elo1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hlam, p901_0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc25, hlam, hphi, p901_1, u5elo1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc35, hlam, hphi, p901_1, u5elo1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc45, hlam, hphi, p901_1, u5elo1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc05, hlam, hphi, p901_1, u5elo2]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc15, hlam, hphi, p901_1, u5elo2]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hlam, p901_0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc35, hlam, hphi, p901_1, u5elo2]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc45, hlam, hphi, p901_1, u5elo2]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc05, hlam, hphi, p901_1, u5elo3]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc15, hlam, hphi, p901_1, u5elo3]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc25, hlam, hphi, p901_1, u5elo3]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hlam, p901_0]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc45, hlam, hphi, p901_1, u5elo3]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hc05, hlam, hphi, p901_1, u5elo4]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [h894, h899, hc04, hc15, hlam, hphi, ht0b, ht5b, p0_1, p901_1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [h899, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p901_1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [h899, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p901_1]
              · have p901_0 := h901c.1
                have p901_1 := h901c.2.1
                have p901_2 := h901c.2.2.1
                have p901_3 := h901c.2.2.2
                linarith only [hlam, p901_0]
          · linarith only [h898, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h928 | h928
        · linarith only [h928, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h930 | h930
          · rcases p0_3 (m.d 4 5) (by simp) with h931 | h931
            · linarith only [h895, h931, hc14, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c | h933c
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hlam, p933_0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc15, hlam, hphi, p933_1, u5elo0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc25, hlam, hphi, p933_1, u5elo0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc35, hlam, hphi, p933_1, u5elo0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc45, hlam, hphi, p933_1, u5elo0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc05, hlam, hphi, p933_1, u5elo1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hlam, p933_0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc25, hlam, hphi, p933_1, u5elo1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc35, hlam, hphi, p933_1, u5elo1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc45, hlam, hphi, p933_1, u5elo1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc05, hlam, hphi, p933_1, u5elo2]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc15, hlam, hphi, p933_1, u5elo2]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hlam, p933_0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc35, hlam, hphi, p933_1, u5elo2]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc45, hlam, hphi, p933_1, u5elo2]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc05, hlam, hphi, p933_1, u5elo3]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc15, hlam, hphi, p933_1, u5elo3]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc25, hlam, hphi, p933_1, u5elo3]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hlam, p933_0]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc45, hlam, hphi, p933_1, u5elo3]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hc05, hlam, hphi, p933_1, u5elo4]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [h931, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p933_1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [h931, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p933_1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [h931, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p933_1]
              · have p933_0 := h933c.1
                have p933_1 := h933c.2.1
                have p933_2 := h933c.2.2.1
                have p933_3 := h933c.2.2.2
                linarith only [hlam, p933_0]
          · linarith only [h930, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h960 | h960
      · rcases p0_3 (m.d 2 4) (by simp) with h961 | h961
        · linarith only [h961, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h963 | h963
          · rcases p0_3 (m.d 4 5) (by simp) with h964 | h964
            · linarith only [h894, h964, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hlam, p966_0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc15, hlam, hphi, p966_1, u5elo0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc25, hlam, hphi, p966_1, u5elo0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc35, hlam, hphi, p966_1, u5elo0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc45, hlam, hphi, p966_1, u5elo0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc05, hlam, hphi, p966_1, u5elo1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hlam, p966_0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc25, hlam, hphi, p966_1, u5elo1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc35, hlam, hphi, p966_1, u5elo1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc45, hlam, hphi, p966_1, u5elo1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc05, hlam, hphi, p966_1, u5elo2]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc15, hlam, hphi, p966_1, u5elo2]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hlam, p966_0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc35, hlam, hphi, p966_1, u5elo2]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc45, hlam, hphi, p966_1, u5elo2]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc05, hlam, hphi, p966_1, u5elo3]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc15, hlam, hphi, p966_1, u5elo3]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc25, hlam, hphi, p966_1, u5elo3]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hlam, p966_0]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc45, hlam, hphi, p966_1, u5elo3]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hc05, hlam, hphi, p966_1, u5elo4]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [h960, h964, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1, p966_1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [h964, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p966_1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [h964, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p966_1]
              · have p966_0 := h966c.1
                have p966_1 := h966c.2.1
                have p966_2 := h966c.2.2.1
                have p966_3 := h966c.2.2.2
                linarith only [hlam, p966_0]
          · linarith only [h963, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h993 | h993
        · linarith only [h993, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h995 | h995
          · rcases p0_3 (m.d 4 5) (by simp) with h996 | h996
            · linarith only [h894, h996, hc04, hc45, hlam, hphi, p0_1]
            · rcases h5bigk with h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hlam, p998_0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc15, hlam, hphi, p998_1, u5elo0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc25, hlam, hphi, p998_1, u5elo0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc35, hlam, hphi, p998_1, u5elo0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc45, hlam, hphi, p998_1, u5elo0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc05, hlam, hphi, p998_1, u5elo1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hlam, p998_0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc25, hlam, hphi, p998_1, u5elo1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc35, hlam, hphi, p998_1, u5elo1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc45, hlam, hphi, p998_1, u5elo1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc05, hlam, hphi, p998_1, u5elo2]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc15, hlam, hphi, p998_1, u5elo2]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hlam, p998_0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc35, hlam, hphi, p998_1, u5elo2]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc45, hlam, hphi, p998_1, u5elo2]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc05, hlam, hphi, p998_1, u5elo3]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc15, hlam, hphi, p998_1, u5elo3]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc25, hlam, hphi, p998_1, u5elo3]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hlam, p998_0]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc45, hlam, hphi, p998_1, u5elo3]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hc05, hlam, hphi, p998_1, u5elo4]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [h996, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p998_1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [h996, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p998_1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [h996, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p998_1]
              · have p998_0 := h998c.1
                have p998_1 := h998c.2.1
                have p998_2 := h998c.2.2.1
                have p998_3 := h998c.2.2.2
                linarith only [hlam, p998_0]
          · linarith only [h995, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h1026 | h1026
    · rcases p0_3 (m.d 1 4) (by simp) with h1027 | h1027
      · rcases p0_3 (m.d 2 4) (by simp) with h1028 | h1028
        · linarith only [h1028, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h1030 | h1030
          · rcases p0_3 (m.d 4 5) (by simp) with h1031 | h1031
            · linarith only [h1031, hlam, p0_0]
            · rcases h5bigk with h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c | h1033c
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hlam, hphi, p1033_1, u5elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc35, hlam, hphi, p1033_1, u5elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h1028, hc24, hlam, hphi, ht45, p1033_1, u5elo0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc05, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc35, hlam, hphi, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h1028, hc24, hlam, hphi, ht45, p1033_1, u5elo1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc05, hlam, hphi, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc35, hlam, hphi, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h1028, hc24, hlam, hphi, ht45, p1033_1, u5elo2]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc05, hlam, hphi, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hlam, hphi, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hlam, hphi, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h1028, hc24, hlam, hphi, ht45, p1033_1, u5elo3]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [h1026, hc04, hc05, hlam, hphi, ht0b, ht5b, p0_1, p1033_1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1033_1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1033_1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1033_1]
              · have p1033_0 := h1033c.1
                have p1033_1 := h1033c.2.1
                have p1033_2 := h1033c.2.2.1
                have p1033_3 := h1033c.2.2.2
                linarith only [hlam, p1033_0]
          · linarith only [h1030, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1060 | h1060
        · linarith only [h1027, h1060, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h1062 | h1062
          · rcases p0_3 (m.d 4 5) (by simp) with h1063 | h1063
            · linarith only [h1063, hlam, p0_0]
            · rcases h5bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc15, hlam, hphi, p1065_1, u5elo0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc25, hlam, hphi, p1065_1, u5elo0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc35, hlam, hphi, p1065_1, u5elo0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1027, hc14, hlam, hphi, ht45, p1065_1, u5elo0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc05, hlam, hphi, p1065_1, u5elo1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc25, hlam, hphi, p1065_1, u5elo1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc35, hlam, hphi, p1065_1, u5elo1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1027, hc14, hlam, hphi, ht45, p1065_1, u5elo1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc05, hlam, hphi, p1065_1, u5elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc15, hlam, hphi, p1065_1, u5elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc35, hlam, hphi, p1065_1, u5elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1027, hc14, hlam, hphi, ht45, p1065_1, u5elo2]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc05, hlam, hphi, p1065_1, u5elo3]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc15, hlam, hphi, p1065_1, u5elo3]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc25, hlam, hphi, p1065_1, u5elo3]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [h1027, hc14, hlam, hphi, ht45, p1065_1, u5elo3]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1065_1]
              · have p1065_0 := h1065c.1
                have p1065_1 := h1065c.2.1
                have p1065_2 := h1065c.2.2.1
                have p1065_3 := h1065c.2.2.2
                linarith only [hlam, p1065_0]
          · linarith only [h1062, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h1092 | h1092
      · rcases p0_3 (m.d 2 4) (by simp) with h1093 | h1093
        · linarith only [h1026, h1093, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h1095 | h1095
          · rcases p0_3 (m.d 4 5) (by simp) with h1096 | h1096
            · linarith only [h1096, hlam, p0_0]
            · rcases h5bigk with h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hlam, p1098_0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc15, hlam, hphi, p1098_1, u5elo0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc25, hlam, hphi, p1098_1, u5elo0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc35, hlam, hphi, p1098_1, u5elo0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1098_1, u5elo0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc05, hlam, hphi, p1098_1, u5elo1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hlam, p1098_0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc25, hlam, hphi, p1098_1, u5elo1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc35, hlam, hphi, p1098_1, u5elo1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1098_1, u5elo1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc05, hlam, hphi, p1098_1, u5elo2]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc15, hlam, hphi, p1098_1, u5elo2]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hlam, p1098_0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc35, hlam, hphi, p1098_1, u5elo2]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1098_1, u5elo2]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc05, hlam, hphi, p1098_1, u5elo3]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc15, hlam, hphi, p1098_1, u5elo3]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc25, hlam, hphi, p1098_1, u5elo3]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hlam, p1098_0]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1098_1, u5elo3]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [h1092, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, p1098_1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1098_1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1098_1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1098_1]
              · have p1098_0 := h1098c.1
                have p1098_1 := h1098c.2.1
                have p1098_2 := h1098c.2.2.1
                have p1098_3 := h1098c.2.2.2
                linarith only [hlam, p1098_0]
          · linarith only [h1095, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h1125 | h1125
        · linarith only [h1026, h1125, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h1127 | h1127
          · rcases p0_3 (m.d 4 5) (by simp) with h1128 | h1128
            · linarith only [h1128, hlam, p0_0]
            · rcases h5bigk with h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hlam, p1130_0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc15, hlam, hphi, p1130_1, u5elo0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc25, hlam, hphi, p1130_1, u5elo0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc35, hlam, hphi, p1130_1, u5elo0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1130_1, u5elo0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc05, hlam, hphi, p1130_1, u5elo1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hlam, p1130_0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc25, hlam, hphi, p1130_1, u5elo1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc35, hlam, hphi, p1130_1, u5elo1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1130_1, u5elo1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc05, hlam, hphi, p1130_1, u5elo2]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc15, hlam, hphi, p1130_1, u5elo2]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hlam, p1130_0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc35, hlam, hphi, p1130_1, u5elo2]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1130_1, u5elo2]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc05, hlam, hphi, p1130_1, u5elo3]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc15, hlam, hphi, p1130_1, u5elo3]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc25, hlam, hphi, p1130_1, u5elo3]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hlam, p1130_0]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [h1026, hc04, hlam, hphi, ht45, p1130_1, u5elo3]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1130_1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1130_1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1130_1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, p1130_1]
              · have p1130_0 := h1130c.1
                have p1130_1 := h1130c.2.1
                have p1130_2 := h1130c.2.2.1
                have p1130_3 := h1130c.2.2.2
                linarith only [hlam, p1130_0]
          · linarith only [h1127, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h4bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi3]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi3]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, hc01, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            rcases p12_3 (m.d 0 4) (by simp) with h17 | h17
                            · rcases p12_3 (m.d 1 4) (by simp) with h18 | h18
                              · linarith only [h0, h18, hlam]
                              · linarith only [h18, h8, hlam]
                            · linarith only [h17, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, hc01, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h6, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hc34, hlam, hphi, ht23, p12_1, u2ehi3]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, h8, h9, hc24, hlam, hphi, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h9, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h8, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · rcases h4bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h6, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p42_1, u2ehi3]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p42_1, u2ehi3]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            rcases p42_3 (m.d 0 4) (by simp) with h46 | h46
                            · rcases p42_3 (m.d 1 4) (by simp) with h47 | h47
                              · linarith only [h0, h47, hlam]
                              · linarith only [h10, h11, h47, h6, hlam]
                            · linarith only [h46, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h0, h11, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h0, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h10, h11, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h0, h11, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h2, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h6, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h2, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h11, h5, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h11, hc04, hc45, hlam, hphi, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h10, h11, h5, h9, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h9, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h11, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h4, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h8, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h10, hlam, p42_0]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [h10, h5, h9, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p42_1]
                          · have p42_0 := h42c.1
                            have p42_1 := h42c.2.1
                            have p42_2 := h42c.2.2.1
                            have p42_3 := h42c.2.2.2
                            linarith only [hlam, p42_0]
                      · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                        · rcases h4bigk with h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c | h75c
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h7, h8, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u2ehi4]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u2ehi2]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u2ehi2]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            rcases p75_3 (m.d 0 4) (by simp) with h80 | h80
                            · rcases p75_3 (m.d 1 4) (by simp) with h81 | h81
                              · linarith only [h0, h81, hlam]
                              · linarith only [h8, h81, hlam]
                            · linarith only [h80, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h0, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h9, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p75_1, u2ehi2]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p75_1, u2ehi2]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p75_1]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h2, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h6, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h9, hlam, p75_1]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p75_1]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h2, hc34, hlam, hphi, ht23, p75_1, u2ehi3]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h7, h8, hc34, hlam, hphi, ht23, p75_1, u2ehi4]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h9, hc34, hlam, hphi, ht23, p75_1, u2ehi2]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            rcases p75_3 (m.d 0 4) (by simp) with h99 | h99
                            · rcases p75_3 (m.d 1 4) (by simp) with h100 | h100
                              · linarith only [h0, h100, hc01, hc45, hlam, hphi, ht0b, ht5b, p75_1]
                              · linarith only [h100, h8, hlam]
                            · linarith only [h4, h99, hlam]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h4, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h8, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h73, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [h74, hlam, p75_0]
                          · have p75_0 := h75c.1
                            have p75_1 := h75c.2.1
                            have p75_2 := h75c.2.2.1
                            have p75_3 := h75c.2.2.2
                            linarith only [hlam, p75_0]
                        · linarith only [h74, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h73, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h4, h6, h8, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo0]
                · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
              · linarith only [h114, h5, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                · linarith only [h114, h116, hc24, hlam, hphi, u2ehi4]
                · linarith only [h116, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · linarith only [h2, h4, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
      · linarith only [h1, h122, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h124 | h124
        · linarith only [h1, h124, hc23, hlam, hphi, u2ehi4]
        · linarith only [h124, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h127 | h127
    · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
      · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
        · rcases m.htr 0 4 5 (by decide) (by decide) with h130 | h130
          · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
            · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
              · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h137 | h137
                        · rcases h4bigk with h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c | h138c
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h0, hlam, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h136, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p138_1, u2ehi4]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h137, hc04, hc45, hlam, hphi, ht0b, ht5b, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            rcases p138_3 (m.d 0 4) (by simp) with h143 | h143
                            · rcases p138_3 (m.d 1 4) (by simp) with h144 | h144
                              · rcases p138_3 (m.d 2 4) (by simp) with h145 | h145
                                · linarith only [h128, h145, hlam]
                                · linarith only [h136, h145, hlam]
                              · linarith only [h134, h144, hlam]
                            · linarith only [h143, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h0, h132, hc01, hc12, hlam, hphi, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h132, h136, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p138_1, u2ehi4]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h132, h137, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            rcases p138_3 (m.d 0 4) (by simp) with h154 | h154
                            · linarith only [h0, h154, hlam]
                            · linarith only [h130, h154, hlam]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h128, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h132, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h128, h137, hc04, hc45, hlam, hphi, ht0b, ht5b, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h131, h135, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h131, h135, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h135, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h131, h135, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p138_1]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h130, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h134, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h136, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [h137, hlam, p138_0]
                          · have p138_0 := h138c.1
                            have p138_1 := h138c.2.1
                            have p138_2 := h138c.2.2.1
                            have p138_3 := h138c.2.2.2
                            linarith only [hlam, p138_0]
                        · rcases h4bigk with h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c | h172c
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h0, hlam, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p172_1, u2ehi3]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            rcases p172_3 (m.d 0 4) (by simp) with h176 | h176
                            · rcases p172_3 (m.d 1 4) (by simp) with h177 | h177
                              · rcases p172_3 (m.d 2 4) (by simp) with h178 | h178
                                · linarith only [h128, h178, hlam]
                                · linarith only [h135, h178, hlam]
                              · linarith only [h0, h136, h137, h177, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h176, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h137, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p172_1, u2ehi3]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            rcases p172_3 (m.d 0 4) (by simp) with h187 | h187
                            · linarith only [h0, h187, hlam]
                            · linarith only [h128, h136, h137, h187, hlam]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h132, h137, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h128, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h132, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h128, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h131, h135, h137, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h137, hc04, hc45, hlam, hphi, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h0, h128, h136, h137, hlam, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h135, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h137, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h130, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h134, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h136, hlam, p172_0]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [h127, h135, h136, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p172_1]
                          · have p172_0 := h172c.1
                            have p172_1 := h172c.2.1
                            have p172_2 := h172c.2.2.1
                            have p172_3 := h172c.2.2.2
                            linarith only [hlam, p172_0]
                      · linarith only [h136, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                        · rcases h4bigk with h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c | h209c
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, hlam, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p209_1, u2ehi3]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h132, h135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            rcases p209_3 (m.d 0 4) (by simp) with h214 | h214
                            · rcases p209_3 (m.d 1 4) (by simp) with h215 | h215
                              · rcases p209_3 (m.d 2 4) (by simp) with h216 | h216
                                · linarith only [h128, h216, hlam]
                                · linarith only [h207, h216, hlam]
                              · linarith only [h134, h215, hlam]
                            · linarith only [h214, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, h132, hc01, hc12, hlam, hphi, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h132, h135, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p209_1, u2ehi2]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h132, h135, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p209_1, u2ehi2]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            rcases p209_3 (m.d 0 4) (by simp) with h225 | h225
                            · linarith only [h0, h225, hlam]
                            · linarith only [h130, h225, hlam]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h128, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h132, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h135, hlam, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h128, hc02, hc45, hlam, hphi, ht0b, ht5b, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h128, hc34, hlam, hphi, ht23, p209_1, u2ehi3]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p209_1]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h135, hc34, hlam, hphi, ht23, p209_1, u2ehi2]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            rcases p209_3 (m.d 0 4) (by simp) with h237 | h237
                            · rcases p209_3 (m.d 1 4) (by simp) with h238 | h238
                              · rcases p209_3 (m.d 2 4) (by simp) with h239 | h239
                                · linarith only [h135, h239, hlam]
                                · linarith only [h207, h239, hlam]
                              · linarith only [h134, h238, hlam]
                            · linarith only [h130, h237, hlam]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h130, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h134, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h207, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [h208, hlam, p209_0]
                          · have p209_0 := h209c.1
                            have p209_1 := h209c.2.1
                            have p209_2 := h209c.2.2.1
                            have p209_3 := h209c.2.2.2
                            linarith only [hlam, p209_0]
                        · linarith only [h135, h208, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h130, h135, h207, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo0]
                  · linarith only [h0, h130, h134, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h129, h133, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
              · linarith only [h131, h132, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h254 | h254
              · linarith only [h131, h254, hc23, hlam, hphi, u2ehi3]
              · linarith only [h0, h128, h254, hlam]
          · linarith only [h128, h130, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h129, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h127, h128, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h260 | h260
      · linarith only [h127, h260, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
        · linarith only [h127, h262, hc23, hlam, hphi, u2ehi4]
        · linarith only [h262, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem n7l_sAB2_H_I_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h15 | h15
    · rcases p0_3 (m.d 1 4) (by simp) with h16 | h16
      · rcases p0_3 (m.d 2 4) (by simp) with h17 | h17
        · linarith only [h17, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 4 5) (by simp) with h20 | h20
            · linarith only [h20, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h20, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h23 | h23
            · linarith only [h23, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h23, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h16, h29, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h16, h32, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h32, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
    · rcases p0_3 (m.d 1 4) (by simp) with h37 | h37
      · rcases p0_3 (m.d 2 4) (by simp) with h38 | h38
        · linarith only [h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h40 | h40
          · linarith only [h40, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h42, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h42, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h45 | h45
        · linarith only [h37, h45, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h47 | h47
          · linarith only [h47, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · linarith only [h37, h49, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h49, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h54 | h54
    · linarith only [h54, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h56 | h56
      · rcases p0_3 (m.d 2 4) (by simp) with h57 | h57
        · linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h56, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · rcases p0_3 (m.d 2 4) (by simp) with h70 | h70
        · linarith only [h70, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · rcases p0_3 (m.d 2 4) (by simp) with h81 | h81
        · linarith only [h81, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h84, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h87, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h87, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h80, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h95 | h95
          · linarith only [h95, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h97 | h97
            · linarith only [h97, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h91, h97, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h92, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · rcases p0_3 (m.d 2 4) (by simp) with h102 | h102
        · linarith only [h102, h91, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · linarith only [h104, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, h91, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h106, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h101, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
    · linarith only [h116, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h118 | h118
      · rcases p0_3 (m.d 2 4) (by simp) with h119 | h119
        · linarith only [h119, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, h122, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · linarith only [h126, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h128, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · linarith only [h136, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h133, h139, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h143 | h143
      · linarith only [h143, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h145 | h145
        · linarith only [h133, h145, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 4 5) (by simp) with h148 | h148
            · linarith only [h133, h148, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h147, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
    · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
      · rcases p0_3 (m.d 2 4) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 4 5) (by simp) with h157 | h157
            · linarith only [h157, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h152, h157, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h161 | h161
        · linarith only [h161, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h153, h164, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h164, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
      · rcases p0_3 (m.d 2 4) (by simp) with h169 | h169
        · linarith only [h169, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 4 5) (by simp) with h172 | h172
            · linarith only [h152, h172, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h168, h172, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h176 | h176
        · linarith only [h176, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h178 | h178
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h168, h179, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h178, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h38, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h126, h134, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h179, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h264, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h284, h295, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h5, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h16 | h16
    · rcases p0_3 (m.d 1 4) (by simp) with h17 | h17
      · rcases p0_3 (m.d 2 4) (by simp) with h18 | h18
        · rcases p0_3 (m.d 3 4) (by simp) with h19 | h19
          · linarith only [h19, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h21, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h17, h18, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h25 | h25
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · linarith only [h26, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h28 | h28
            · linarith only [h17, h28, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h28, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h25, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
    · linarith only [h16, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · linarith only [h34, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · rcases p0_3 (m.d 4 5) (by simp) with h39 | h39
            · linarith only [h39, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h39, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h42, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h42, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h37, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h49 | h49
    · rcases p0_3 (m.d 1 4) (by simp) with h50 | h50
      · rcases p0_3 (m.d 2 4) (by simp) with h51 | h51
        · rcases p0_3 (m.d 3 4) (by simp) with h52 | h52
          · linarith only [h52, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h54 | h54
            · linarith only [h54, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h49, h54, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h51, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h50, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h59 | h59
      · rcases p0_3 (m.d 2 4) (by simp) with h60 | h60
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h49, h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h69 | h69
    · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · rcases p0_3 (m.d 3 4) (by simp) with h73 | h73
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · linarith only [h74, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h74, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h77 | h77
            · linarith only [h77, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h72, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h81 | h81
        · rcases p0_3 (m.d 3 4) (by simp) with h82 | h82
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h86, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h86, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h81, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · rcases p0_3 (m.d 1 4) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · linarith only [h95, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h90, h95, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h98, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h106, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h109 | h109
            · linarith only [h109, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h109, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h123, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h130 | h130
      · rcases p0_3 (m.d 2 4) (by simp) with h131 | h131
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h114, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h130, h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h131, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h138 | h138
        · rcases p0_3 (m.d 3 4) (by simp) with h139 | h139
          · linarith only [h139, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h141 | h141
            · linarith only [h114, h141, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h141, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h138, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
    · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h148 | h148
      · rcases p0_3 (m.d 2 4) (by simp) with h149 | h149
        · rcases p0_3 (m.d 3 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 4 5) (by simp) with h151 | h151
            · linarith only [h151, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, h151, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h150, hlam, p0_0]
        · linarith only [h149, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h156 | h156
        · rcases p0_3 (m.d 3 4) (by simp) with h157 | h157
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, h158, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h157, hlam, p0_0]
        · linarith only [h156, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h164, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h163, h168, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h167, hlam, p0_0]
        · linarith only [h166, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h173 | h173
      · linarith only [h173, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h175 | h175
        · rcases p0_3 (m.d 3 4) (by simp) with h176 | h176
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · linarith only [h163, h177, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h175, h177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h176, hlam, p0_0]
        · linarith only [h175, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht23, ht34, ht45, p0_1, u2ehi3, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_R_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h2bigk := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, h3, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h12, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · linarith only [h15, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, h2, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                    · linarith only [h1, h21, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h21, hc45, hlam, hphi, u4ehi1]
          · linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
          · linarith only [h25, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h28, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h25, h30, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h27, h3, h32, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h1, h34, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h34, hc45, hlam, hphi, u4ehi1]
            · linarith only [h2, h27, h3, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h38 | h38
        · linarith only [h2, h38, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h40 | h40
          · linarith only [h2, h40, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
            · linarith only [h0, h2, h42, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
              · linarith only [h0, h1, h2, h38, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h40, h46, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h1, h49, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h49, hc45, hlam, hphi, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h1, h52, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h52, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h55 | h55
      · rcases m.htr 0 2 4 (by decide) (by decide) with h56 | h56
        · linarith only [h0, h1, h56, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h58 | h58
          · linarith only [h0, h1, h58, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
            · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
              · linarith only [h0, h1, h56, h61, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h1, h58, h61, h63, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                  · linarith only [h0, h1, h60, h61, h65, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1, h60, h65, hc23, hc34, hlam, hphi]
            · linarith only [h55, h58, h60, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h69 | h69
        · linarith only [h0, h1, h69, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h71 | h71
          · linarith only [h55, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
            · linarith only [h0, h1, h55, h73, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
              · linarith only [h0, h55, h69, h75, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h77, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                            · linarith only [h73, h79, h84, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h84, hc45, hlam, hphi, u4ehi3]
                          · linarith only [h73, h79, h80, h83, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1, h73, h79, h82, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h73, h79, h80, h81, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h1, h80, hc45, hlam, hphi, u4ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                      · linarith only [h79, h91, h92, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h92, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                            · rcases h2bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h1, h75, hc12, hc24, hlam, hphi, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h55, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h69, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h71, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h73, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h75, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h77, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h94, h97, hc02, hc34, hlam, hphi, ht23, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h94, h97, hc12, hc34, hlam, hphi, ht23, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h92, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h94, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h114 | h114
                                · linarith only [h114, hlam, p98_0]
                                · rcases p98_3 (m.d 1 2) (by simp) with h116 | h116
                                  · linarith only [h116, h75, hlam]
                                  · rcases p98_3 (m.d 2 3) (by simp) with h118 | h118
                                    · linarith only [h118, h92, hlam]
                                    · linarith only [h118, h55, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h121 | h121
                                · linarith only [h121, h69, hlam]
                                · linarith only [h0, h121, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h55, h92, hc12, hc34, hlam, hphi, ht23, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h77, h91, h92, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u4ehi4]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h127 | h127
                                · linarith only [h127, hlam, p98_0]
                                · rcases p98_3 (m.d 1 2) (by simp) with h129 | h129
                                  · linarith only [h129, h77, hlam]
                                  · rcases p98_3 (m.d 2 3) (by simp) with h131 | h131
                                    · linarith only [h131, h94, hlam]
                                    · linarith only [h131, h55, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h134 | h134
                                · linarith only [h134, h71, hlam]
                                · linarith only [h0, h134, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h55, hc12, hc25, hlam, hphi, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h96, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                            · linarith only [h75, h92, h97, hc45, hlam, hphi, u4ehi1]
                          · linarith only [h75, h91, h96, hlam]
                    · linarith only [h91, hc45, hlam, hphi, u4ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h143 | h143
    · linarith only [h0, h143, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h145 | h145
      · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
        · rcases m.htr 0 2 5 (by decide) (by decide) with h147 | h147
          · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
            · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                      · linarith only [h145, h153, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                        · linarith only [h148, h151, h153, h155, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h0, h146, h157, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h157, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h152, hc45, hlam, hphi, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                      · linarith only [h0, h145, h162, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                        · linarith only [h0, h145, h164, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                          · linarith only [h0, h146, h166, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h161, h166, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h161, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h147, h150, hlam]
              · linarith only [h0, h143, h146, h147, h149, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h145, h148, hlam]
          · linarith only [h146, h147, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h174 | h174
          · linarith only [h146, h174, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
            · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
              · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h145, h146, h177, h181, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h145, h146, h176, h179, h181, h183, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                          · linarith only [h176, h179, h181, h185, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h146, h185, hc45, hlam, hphi, u4ehi0]
                    · linarith only [h180, hc45, hlam, hphi, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                      · linarith only [h145, h179, h189, h190, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                        · linarith only [h145, h146, h177, h192, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h194 | h194
                          · linarith only [h177, h194, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h146, h189, h194, hc01, hc14, hlam, hphi]
                    · linarith only [h189, hc45, hlam, hphi, u4ehi1]
                · linarith only [h145, h146, h177, h178, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                · linarith only [h145, h174, h177, h199, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                  · linarith only [h176, h177, h201, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                      · linarith only [h145, h201, h203, h204, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                        · linarith only [h0, h145, h177, h204, h206, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h208 | h208
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                            · rcases h2bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, h199, h204, h208, hc23, hc34, hlam, hphi, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h146, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h174, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h199, h204, h208, hc02, hc34, hlam, hphi, ht23, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h199, h204, h208, hc23, hc34, hlam, hphi, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h177, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h199, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h145, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h176, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h204, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h206, hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h145, h204, hc23, hc34, hlam, hphi, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, h204, hc01, hc34, hlam, hphi, ht12, ht23, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                rcases p210_3 (m.d 0 2) (by simp) with h228 | h228
                                · linarith only [h146, h228, hlam]
                                · linarith only [h145, h228, hlam]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p210_1, u5ehi2]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h145, h206, hc23, hc35, hlam, hphi, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h0, h206, hc01, hc35, hlam, hphi, ht12, ht23, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                rcases p210_3 (m.d 0 2) (by simp) with h235 | h235
                                · linarith only [h174, h235, hlam]
                                · linarith only [h145, h235, hlam]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [h208, hlam, p210_1]
                              · have p210_0 := h210c.1
                                have p210_1 := h210c.2.1
                                have p210_2 := h210c.2.2.1
                                have p210_3 := h210c.2.2.2
                                linarith only [hlam, p210_0]
                            · linarith only [h203, h204, h209, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h177, h203, h208, hlam]
                    · linarith only [h143, h203, hc45, hlam, hphi, u4ehi0]
            · linarith only [h0, h145, h146, h176, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h244 | h244
        · linarith only [h145, h244, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h246 | h246
          · linarith only [h145, h246, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
            · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
              · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
                · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h248, h253, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h145, h251, h253, hc01, hc13, hlam, hphi]
                    · linarith only [h252, hc45, hlam, hphi, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                      · linarith only [h251, h257, h258, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
                        · linarith only [h248, h251, h260, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                          · linarith only [h249, h262, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h257, h262, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h257, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h145, h248, h250, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h145, h248, h249, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h268 | h268
              · linarith only [h248, h268, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
                · linarith only [h248, h270, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                            · linarith only [h272, h277, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h273, h277, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h268, h273, h276, hlam]
                        · linarith only [h268, h273, h274, h275, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h248, h272, h273, h274, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h273, hc45, hlam, hphi, u4ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                      · linarith only [h0, h248, h272, h285, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h248, h285, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h284, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB2_M_IR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5emax := hb5.2.2
  have h2elo := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, ht45, u4ehi0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h6, hlam, ht45, u4ehi4]
        · linarith only [h0, h6, hlam, ht45, u4ehi0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, hlam, ht45, u4ehi4]
        · linarith only [h0, h10, hlam, ht45, u4ehi0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
        · linarith only [h0, h13, hlam, ht45, u4ehi4]
        · linarith only [h0, h13, hlam, ht45, u4ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h16 | h16
    · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h22, hlam, ht45, u4ehi4]
                · linarith only [h0, h22, hlam, ht45, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                · linarith only [h0, h25, hlam, ht45, u4ehi4]
                · linarith only [h0, h25, hlam, ht45, u4ehi1]
            · linarith only [h0, h19, h20, hc23, hlam, ht34, ht45]
          · linarith only [h16, h19, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
          · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h18, h33, hlam, ht45, u4ehi0]
                · linarith only [h0, h33, hlam, ht45, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                · linarith only [h0, h18, h36, hlam, ht45, u4ehi0]
                · linarith only [h0, h36, hlam, ht45, u4ehi1]
            · linarith only [h0, h30, h31, hc23, hlam, ht34, ht45]
          · linarith only [h16, h30, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
        · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
              · linarith only [h0, h17, h44, hc03, hlam, ht34, ht45]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h46, hlam, ht45, u4ehi4]
                · linarith only [h0, h46, hlam, ht45, u4ehi1]
            · linarith only [h0, h42, h43, hc23, hlam, ht34, ht45]
          · linarith only [h16, h42, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
          · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
            · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h16, h17, h53, hc23, hlam, ht34, ht45]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h41, h55, hlam, ht45, u4ehi0]
                · linarith only [h0, h55, hlam, ht45, u4ehi1]
            · linarith only [h0, h51, h52, hc23, hlam, ht34, ht45]
          · linarith only [h16, h51, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
      · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
        · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
          · linarith only [h16, h62, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
            · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
              · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                · linarith only [h0, h66, hlam, ht45, u4ehi4]
                · linarith only [h0, h66, hlam, ht45, u4ehi1]
              · linarith only [h16, h60, h62, h64, h65, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
                · linarith only [h0, h71, hlam, ht45, u4ehi4]
                · linarith only [h0, h71, hlam, ht45, u4ehi1]
              · linarith only [h16, h60, h62, h70, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
          · linarith only [h16, h75, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
            · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                · linarith only [h0, h61, h79, hlam, ht45, u4ehi0]
                · linarith only [h0, h79, hlam, ht45, u4ehi1]
              · linarith only [h16, h60, h75, h77, h78, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
              · rcases m.htr 1 4 5 (by decide) (by decide) with h84 | h84
                · linarith only [h0, h84, hlam, ht45, u4ehi4]
                · linarith only [h0, h84, hlam, ht45, u4ehi1]
              · linarith only [h16, h60, h75, h83, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h88 | h88
        · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
          · linarith only [h16, h89, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
              · linarith only [h16, h60, h89, h92, hc02, hlam, hphi, u2elo2]
              · linarith only [h0, h89, h91, h92, hc25, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
              · linarith only [h16, h60, h89, h95, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                · linarith only [h0, h97, hlam, ht45, u4ehi4]
                · linarith only [h0, h97, hlam, ht45, u4ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
          · linarith only [h100, h16, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
            · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
              · linarith only [h100, h103, h16, h60, hc02, hlam, hphi, u2elo2]
              · linarith only [h0, h100, h102, h103, hc25, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
              · linarith only [h100, h106, h16, h60, hc02, hlam, hphi, u2elo2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                · linarith only [h0, h108, h88, hlam, ht45, u4ehi0]
                · linarith only [h0, h108, hlam, ht45, u4ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h111 | h111
    · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
      · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
        · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
          · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
            · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
              · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                  · linarith only [h111, h118, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                      · linarith only [h0, h121, hlam, ht45, u4ehi4]
                      · linarith only [h0, h121, hlam, ht45, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                      · linarith only [h0, h124, hlam, ht45, u4ehi4]
                      · linarith only [h0, h124, hlam, ht45, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                  · linarith only [h111, h127, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h117, h130, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h0, h130, hlam, ht45, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                      · linarith only [h117, h133, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h0, h133, hlam, ht45, u4ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                  · linarith only [h111, h137, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h116, h137, h139, hc13, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h141 | h141
                      · linarith only [h0, h141, hlam, ht45, u4ehi4]
                      · linarith only [h111, h112, h116, h136, h141, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                  · linarith only [h111, h144, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                    · linarith only [h114, h116, h146, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                      · linarith only [h136, h148, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h0, h148, hlam, ht45, u4ehi2]
            · linarith only [h0, h115, hc12, hlam, ht23, ht34, ht45]
          · linarith only [h111, h114, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
          · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
            · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
              · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                  · linarith only [h111, h157, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                      · linarith only [h113, h160, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h160, hlam, ht45, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h113, h163, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h163, hlam, ht45, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                  · linarith only [h111, h166, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h169 | h169
                      · linarith only [h113, h169, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h169, hlam, ht45, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                      · linarith only [h113, h172, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h172, hlam, ht45, u4ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                · linarith only [h111, h112, h113, h155, h175, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                  · linarith only [h111, h177, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                    · linarith only [h153, h155, h179, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                      · linarith only [h113, h181, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h181, hlam, ht45, u4ehi2]
            · linarith only [h0, h154, hc12, hlam, ht23, ht34, ht45]
          · linarith only [h111, h153, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
        · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
          · rcases m.htr 1 2 5 (by decide) (by decide) with h188 | h188
            · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
              · rcases m.htr 1 4 5 (by decide) (by decide) with h190 | h190
                · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                  · linarith only [h111, h112, h187, h189, h191, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h193 | h193
                    · linarith only [h111, h112, h193, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                      · linarith only [h0, h195, hlam, ht45, u4ehi4]
                      · linarith only [h112, h186, h187, h189, h195, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                · linarith only [h112, h186, h187, h189, h190, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                  · linarith only [h111, h200, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                    · linarith only [h111, h189, h202, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h0, h204, hlam, ht45, u4ehi4]
                      · linarith only [h0, h204, hlam, ht45, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · linarith only [h111, h207, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                    · linarith only [h111, h112, h209, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
                      · linarith only [h199, h211, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h0, h211, hlam, ht45, u4ehi2]
            · linarith only [h0, h188, hc12, hlam, ht23, ht34, ht45]
          · linarith only [h111, h187, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
          · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
            · rcases m.htr 1 3 5 (by decide) (by decide) with h218 | h218
              · rcases m.htr 1 4 5 (by decide) (by decide) with h219 | h219
                · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                  · linarith only [h111, h112, h216, h218, h220, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h222 | h222
                    · linarith only [h111, h112, h222, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                      · linarith only [h186, h224, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h224, hlam, ht45, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                  · linarith only [h111, h112, h216, h218, h227, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                    · linarith only [h111, h112, h229, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                      · linarith only [h186, h231, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h231, hlam, ht45, u4ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                  · linarith only [h111, h235, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                    · linarith only [h111, h218, h237, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                      · linarith only [h186, h239, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h239, hlam, ht45, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                  · linarith only [h111, h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                    · linarith only [h111, h112, h244, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                      · linarith only [h186, h246, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h246, hlam, ht45, u4ehi2]
            · linarith only [h0, h217, hc12, hlam, ht23, ht34, ht45]
          · linarith only [h111, h216, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h251 | h251
      · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
        · rcases m.htr 1 2 3 (by decide) (by decide) with h253 | h253
          · linarith only [h111, h253, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h255 | h255
            · rcases m.htr 1 3 5 (by decide) (by decide) with h256 | h256
              · rcases m.htr 1 4 5 (by decide) (by decide) with h257 | h257
                · rcases m.htr 2 3 4 (by decide) (by decide) with h258 | h258
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                      · linarith only [h253, h255, h260, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                      · linarith only [h253, h255, h257, h258, h260, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                    · linarith only [h251, h253, h255, h259, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                      · linarith only [h0, h265, hlam, ht45, u4ehi4]
                      · linarith only [h253, h255, h257, h258, h265, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h111, h251, h264, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                      · linarith only [h257, h269, h271, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi1]
                      · linarith only [h253, h255, h269, h271, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                    · linarith only [h111, h251, h270, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                      · linarith only [h257, h276, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h111, h251, h252, h269, h276, hlam]
                    · linarith only [h111, h251, h275, hlam]
              · linarith only [h111, h251, h253, h256, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h255, hc12, hlam, ht23, ht34, ht45]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
          · linarith only [h111, h282, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
            · rcases m.htr 1 3 5 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 4 5 (by decide) (by decide) with h286 | h286
                · linarith only [h252, h282, h284, h286, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h290 | h290
                      · linarith only [h252, h290, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h0, h288, h290, hlam, ht45, u4ehi3]
                    · linarith only [h251, h282, h284, h289, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h294 | h294
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                      · linarith only [h286, h295, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h282, h284, h286, h288, h295, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h111, h251, h294, hlam]
              · linarith only [h111, h251, h282, h285, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h284, hc12, hlam, ht23, ht34, ht45]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
        · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
          · linarith only [h111, h302, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
            · rcases m.htr 1 3 5 (by decide) (by decide) with h305 | h305
              · linarith only [h111, h251, h302, h305, hc02, hlam, hphi, u2elo2]
              · linarith only [h302, h304, h305, hlam]
            · linarith only [h0, h304, hc12, hlam, ht23, ht34, ht45]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
          · linarith only [h111, h309, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
            · rcases m.htr 1 3 5 (by decide) (by decide) with h312 | h312
              · linarith only [h111, h251, h309, h312, hc02, hlam, hphi, u2elo2]
              · linarith only [h309, h311, h312, hlam]
            · linarith only [h0, h311, hc12, hlam, ht23, ht34, ht45]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h316 | h316
    · rcases m.htr 0 3 5 (by decide) (by decide) with h317 | h317
      · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
        · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
          · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
            · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
              · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
                · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                  · linarith only [h316, h323, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h326 | h326
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
                        · linarith only [h0, h327, hlam, ht45, u4ehi4]
                        · linarith only [h323, h325, h326, h327, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                      · linarith only [h323, h325, h326, hlam]
                    · linarith only [h0, h325, hc23, hlam, ht34, ht45]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                  · linarith only [h316, h332, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h322, h335, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h332, h334, h335, hlam]
                    · linarith only [h0, h334, hc23, hlam, ht34, ht45]
              · linarith only [h0, h321, hc13, hlam, ht34, ht45]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
              · linarith only [h319, h320, h340, hlam]
              · linarith only [h0, h340, hc13, hlam, ht34, ht45]
          · linarith only [h316, h319, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
          · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
            · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
              · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                  · linarith only [h316, h348, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                      · linarith only [h318, h351, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h348, h350, h351, hlam]
                    · linarith only [h0, h350, hc23, hlam, ht34, ht45]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                  · linarith only [h316, h355, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                      · linarith only [h347, h358, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h355, h357, h358, hlam]
                    · linarith only [h0, h357, hc23, hlam, ht34, ht45]
              · linarith only [h0, h346, hc13, hlam, ht34, ht45]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
              · linarith only [h344, h345, h363, hlam]
              · linarith only [h0, h363, hc13, hlam, ht34, ht45]
          · linarith only [h316, h344, hc12, hlam, hphi, u2elo0]
      · linarith only [h0, h317, hc03, hlam, ht34, ht45]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h368 | h368
      · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
        · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
          · linarith only [h316, h370, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
            · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
              · rcases m.htr 1 4 5 (by decide) (by decide) with h374 | h374
                · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
                      · linarith only [h370, h372, h377, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                      · linarith only [h370, h372, h374, h377, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                    · linarith only [h0, h370, h376, hc12, hlam, ht23, ht34, ht45]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                      · linarith only [h370, h372, h375, h382, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h370, h372, h374, h375, h382, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h370, h381, hc12, hlam, ht23, ht34, ht45]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h388 | h388
                      · linarith only [h374, h388, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h370, h372, h386, h388, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                    · linarith only [h0, h370, h387, hc12, hlam, ht23, ht34, ht45]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
                      · linarith only [h374, h393, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h316, h368, h369, h386, h393, hlam]
                    · linarith only [h0, h316, h368, h369, h374, h392, hlam, ht45, u4ehi1]
              · linarith only [h0, h370, h372, h373, hc25, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h398 | h398
              · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h401 | h401
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h402 | h402
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h400, h403, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                        · linarith only [h400, h402, h403, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                      · linarith only [h372, h399, h402, hlam]
                    · linarith only [h0, h316, h401, hc03, hlam, ht34, ht45]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
                        · linarith only [h0, h410, hlam, ht45, u4ehi4]
                        · linarith only [h316, h400, h409, h410, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h316, h368, h369, h400, h409, hlam]
                    · linarith only [h0, h316, h408, hc03, hlam, ht34, ht45]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                      · linarith only [h399, h417, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h419 | h419
                        · linarith only [h415, h417, h419, hlam]
                        · linarith only [h0, h419, hlam, ht45, u4ehi3]
                    · linarith only [h0, h316, h416, hc02, hlam, ht23, ht34, ht45]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
                      · linarith only [h399, h424, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h316, h368, h369, h415, h424, hlam]
                    · linarith only [h0, h316, h368, h369, h399, h423, hlam, ht45, u4ehi1]
              · linarith only [h0, h398, hc13, hlam, ht34, ht45]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
          · linarith only [h316, h429, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
            · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
              · rcases m.htr 1 4 5 (by decide) (by decide) with h433 | h433
                · linarith only [h369, h429, h431, h433, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                      · linarith only [h369, h437, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h429, h431, h435, h437, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                    · linarith only [h368, h429, h431, h436, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h441 | h441
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h442 | h442
                      · linarith only [h369, h442, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h429, h431, h433, h435, h442, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h0, h429, h431, h433, h441, hlam, ht45, u4ehi1]
              · linarith only [h0, h429, h432, hc12, hlam, ht23, ht34, ht45]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
              · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h451 | h451
                      · linarith only [h369, h449, h451, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                      · linarith only [h431, h448, h451, hlam]
                    · linarith only [h0, h450, hc23, hlam, ht34, ht45]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                      · linarith only [h369, h456, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · linarith only [h429, h447, h448, h449, h456, hlam]
                    · linarith only [h0, h316, h455, hc03, hlam, ht34, ht45]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                      · linarith only [h369, h462, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h464 | h464
                        · linarith only [h460, h462, h464, hlam]
                        · linarith only [h0, h464, hlam, ht45, u4ehi3]
                    · linarith only [h0, h460, h461, hlam, ht45, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h469 | h469
                      · linarith only [h448, h469, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                      · linarith only [h460, h468, h469, hlam]
                    · linarith only [h316, h368, h468, hlam]
              · linarith only [h0, h447, hc13, hlam, ht34, ht45]
      · linarith only [h0, h368, hc03, hlam, ht34, ht45]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sAB2_M_IR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_IR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h3, h7, h8, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, h2, h7, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h13, h15, h2, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h15, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h18, h19, h3, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h18, h2, h22, h4, h5, h6, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h24, h5, h6, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h18, h26, h5, h6, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h18, h2, h26, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
              · linarith only [h1, h29, h5, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h32, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h3, h31, h32, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h31, h35, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h29, h37, h5, hc24, hlam, hphi, u2ehi1]
                    · linarith only [h0, h2, h37, h4, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
              · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h43, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h3, h4, h40, h41, h42, h43, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h2, h4, h40, h41, h42, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                  · linarith only [h0, h48, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h3, h4, h47, h48, hc45, hlam, hphi, u4ehi3]
                · linarith only [h2, h4, h47, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h1, h4, h40, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
          · linarith only [h2, h3, h53, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
            · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
              · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                  · linarith only [h0, h58, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h1, h53, h60, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h0, h1, h53, h57, h62, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h3, h55, h56, h57, h62, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h2, h3, h57, hc35, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                  · linarith only [h0, h3, h67, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                    · linarith only [h1, h53, h69, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h3, h53, h66, h71, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h3, h66, h71, hc45, hlam, hphi, u4ehi3]
                · linarith only [h2, h3, h66, hc35, hlam, hphi, ht23, u2ehi2]
            · linarith only [h1, h2, h3, h55, hc35, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
        · linarith only [h2, h76, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
          · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
            · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
              · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                · linarith only [h0, h2, h81, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                  · linarith only [h0, h76, h83, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h79, h85, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h2, h78, h85, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h2, h78, h79, h80, hc34, hlam, hphi, ht23, u2ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
              · linarith only [h1, h79, h89, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h2, h78, h79, h89, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                · linarith only [h0, h2, h78, h92, h93, h94, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h0, h76, h96, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                    · linarith only [h1, h78, h98, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                      · linarith only [h0, h100, h2, h78, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h100, h2, h92, h93, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                · linarith only [h0, h103, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h0, h105, h76, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                    · linarith only [h1, h107, h93, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                      · linarith only [h1, h109, h78, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h109, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h1, h78, h92, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h114 | h114
    · linarith only [h0, h114, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
      · rcases m.htr 0 3 5 (by decide) (by decide) with h117 | h117
        · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
          · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
            · linarith only [h114, h118, h119, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
              · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                      · linarith only [h116, h125, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h4bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h0, h116, h121, h125, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h114, hlam, p127_1]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          rcases p127_3 (m.d 0 4) (by simp) with h131 | h131
                          · rcases p127_3 (m.d 1 4) (by simp) with h132 | h132
                            · rcases p127_3 (m.d 2 4) (by simp) with h133 | h133
                              · rcases p127_3 (m.d 3 4) (by simp) with h134 | h134
                                · linarith only [h116, h134, hlam]
                                · rcases p127_3 (m.d 4 5) (by simp) with h136 | h136
                                  · linarith only [h118, h136, hlam]
                                  · linarith only [h125, h136, hlam]
                              · linarith only [h122, h133, hlam]
                            · linarith only [h0, h116, h121, h132, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p127_1, u5ehi1]
                          · linarith only [h116, h131, hlam]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h0, h116, h125, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h118, h125, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h119, hlam, p127_1]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          rcases p127_3 (m.d 0 4) (by simp) with h146 | h146
                          · rcases p127_3 (m.d 1 4) (by simp) with h147 | h147
                            · rcases p127_3 (m.d 2 4) (by simp) with h148 | h148
                              · rcases p127_3 (m.d 3 4) (by simp) with h149 | h149
                                · linarith only [h149, hlam, p127_0]
                                · rcases p127_3 (m.d 4 5) (by simp) with h151 | h151
                                  · linarith only [h121, h151, hlam]
                                  · linarith only [h125, h151, hlam]
                              · linarith only [h122, h148, hlam]
                            · linarith only [h147, hlam, p127_0]
                          · linarith only [h116, h146, hlam]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h125, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h118, h125, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h119, hc24, hlam, hphi, p127_1, u2ehi1]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          rcases p127_3 (m.d 0 4) (by simp) with h161 | h161
                          · linarith only [h114, h161, hlam]
                          · linarith only [h116, h161, hlam]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h122, h125, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h116, hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h121, h125, hlam, p127_1]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h122, hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h125, hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h118, hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h121, hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h124, hlam, p127_0]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [h118, hc04, hlam, hphi, ht0b, ht45, ht5b, p127_1, u4ehi3]
                        · have p127_0 := h127c.1
                          have p127_1 := h127c.2.1
                          have p127_2 := h127c.2.2.1
                          have p127_3 := h127c.2.2.2
                          linarith only [hlam, p127_0]
                    · linarith only [h114, h118, h124, hlam]
                  · linarith only [h114, h118, h122, h123, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h0, h116, h118, h122, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · linarith only [h0, h116, h118, h119, h121, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
            · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
              · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                    · linarith only [h114, h118, h183, hc24, hlam, hphi, u2ehi0]
                    · linarith only [h114, h179, h180, h183, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h0, h117, h182, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h116, h117, h118, h179, h180, h181, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · linarith only [h114, h179, h180, hc45, hlam, hphi, ht23, ht34, u2ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
              · linarith only [h114, h118, h179, h189, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
                    · linarith only [h114, h118, h191, h193, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h114, h193, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h0, h117, h192, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h117, h191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
          · linarith only [h116, h117, h198, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
            · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h114, h116, h117, h198, h200, h201, h203, hc12, hc23, hlam, hphi, ht01, ht0b, ht45, ht5b, u2ehi0, u4ehi3]
                  · linarith only [h0, h203, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h0, h116, h202, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h114, h200, h201, hc45, hlam, hphi, ht23, ht34, u2ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
              · linarith only [h114, h198, h200, h208, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                · rcases m.htr 2 3 5 (by decide) (by decide) with h211 | h211
                  · linarith only [h116, h117, h211, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h211, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h0, h116, h210, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h215 | h215
        · linarith only [h116, h215, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h217 | h217
          · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
            · linarith only [h114, h217, h218, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h220 | h220
              · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                · linarith only [h0, h116, h221, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h221, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h114, h217, h218, h220, hc24, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
            · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
              · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                · linarith only [h0, h116, h227, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h227, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h114, h225, h226, hc45, hlam, hphi, ht23, ht34, u2ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
              · linarith only [h114, h217, h225, h231, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                · linarith only [h0, h116, h233, hc23, hlam, hphi, u2ehi0]
                · linarith only [h0, h233, hc34, hlam, hphi, ht23, u2ehi0]

theorem n7l_sAB2_M_IR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h2elo := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
              · linarith only [h1, h2, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h1, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
              · linarith only [h1, h2, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
          · linarith only [h1, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
        · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h15, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
            · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
              · linarith only [h0, h14, h18, h2, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h14, h17, h2, h20, hlam]
                · rcases h4bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, h17, h2, hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h17, h2, hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h2, hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h2, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, h17, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, h2, hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h15, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h1, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h18, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h17, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo2, u4ehi0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, h17, hlam, p22_1]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h17, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h20, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hc45, hlam, hphi, p22_1, u4ehi0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, h17, hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h17, hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hc45, hlam, hphi, p22_1, u4ehi3]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
              · linarith only [h1, h2, h48, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                · rcases h4bigk with h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h14, h2, h50, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p51_1, u4ehi2]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h2, h50, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p51_1, u4ehi2]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h2, h50, hlam, p51_1]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h2, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h0, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p51_1, u4ehi2]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h0, h2, h50, hlam, p51_1]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h15, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h1, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h14, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h17, hlam, p51_1]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h48, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    rcases p51_3 (m.d 0 4) (by simp) with h67 | h67
                    · linarith only [h67, hlam, p51_0]
                    · rcases p51_3 (m.d 1 4) (by simp) with h69 | h69
                      · linarith only [h0, h2, h50, h69, hlam]
                      · rcases p51_3 (m.d 2 4) (by simp) with h71 | h71
                        · linarith only [h17, h71, hlam]
                        · rcases p51_3 (m.d 3 4) (by simp) with h73 | h73
                          · rcases p51_3 (m.d 4 5) (by simp) with h74 | h74
                            · linarith only [h50, h74, hlam]
                            · linarith only [h2, h74, hlam]
                          · linarith only [h73, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    rcases p51_3 (m.d 0 4) (by simp) with h78 | h78
                    · linarith only [h2, h50, h78, hlam]
                    · linarith only [h0, h78, hlam]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    rcases p51_3 (m.d 0 4) (by simp) with h81 | h81
                    · linarith only [h2, h50, h81, hlam]
                    · linarith only [h1, h81, hlam]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p51_1, u4ehi0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p51_1, u4ehi1]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h14, hc45, hlam, hphi, p51_1, u4ehi2]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [hc45, hlam, hphi, p51_1, u4ehi2]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [h50, hlam, p51_0]
                  · have p51_0 := h51c.1
                    have p51_1 := h51c.2.1
                    have p51_2 := h51c.2.2.1
                    have p51_3 := h51c.2.2.2
                    linarith only [hlam, p51_0]
                · rcases h4bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h1, h14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p91_1, u2elo0, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p91_1, u2elo0, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h2, hc45, hlam, hphi, p91_1, u4ehi3]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h2, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h0, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p91_1, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h0, h17, h2, hc23, hc45, hlam, hphi, ht34, p91_1]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h15, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h1, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h14, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h17, hlam, p91_1]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h48, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h50, hc45, hlam, hphi, p91_1, u4ehi0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h14, h50, hc45, hlam, hphi, p91_1, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h50, hc45, hlam, hphi, p91_1, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h50, hlam, p91_0]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h0, h14, hc45, hlam, hphi, p91_1, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [h14, hc45, hlam, hphi, p91_1, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hc45, hlam, hphi, p91_1, u4ehi2]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hc45, hlam, hphi, p91_1, u4ehi3]
                  · have p91_0 := h91c.1
                    have p91_1 := h91c.2.1
                    have p91_2 := h91c.2.2.1
                    have p91_3 := h91c.2.2.2
                    linarith only [hlam, p91_0]
        · linarith only [h1, h14, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
      · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
        · linarith only [h1, h119, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
          · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
            · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
              · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                · linarith only [h122, h124, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                · linarith only [h0, h1, h121, h124, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · linarith only [h0, h1, h121, h123, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
              · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                · rcases h4bigk with h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p130_1, u2elo3, u4ehi1]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h1, hlam, p130_1]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h1, h122, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p130_1, u2elo3]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p130_1, u2elo3, u4ehi4]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h0, hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h119, hlam, p130_1]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h0, h1, h122, hc01, hlam, hphi, ht0b, ht45, ht5b, p130_1, u4ehi0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p130_1, u2elo3, u4ehi4]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p130_1, u2elo3, u4ehi0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p130_1, u2elo3, u4ehi1]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h122, hlam, p130_1]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p130_1, u2elo3, u4ehi4]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h0, h121, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p130_1, u4ehi4]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h121, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p130_1, u4ehi4]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h119, hc12, hc34, hlam, hphi, ht23, p130_1]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    rcases p130_3 (m.d 0 4) (by simp) with h150 | h150
                    · linarith only [h1, h122, h150, hlam]
                    · linarith only [h118, h150, hlam]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h118, hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h121, hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h128, hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [h129, hlam, p130_0]
                  · have p130_0 := h130c.1
                    have p130_1 := h130c.2.1
                    have p130_2 := h130c.2.2.1
                    have p130_3 := h130c.2.2.2
                    linarith only [hlam, p130_0]
                · linarith only [h0, h1, h121, h122, h129, hlam]
              · linarith only [h0, h1, h121, h128, hlam]
          · linarith only [h1, h118, h121, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
        · linarith only [h1, h161, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
          · linarith only [h0, h118, h163, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
            · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
              · linarith only [h0, h118, h166, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                · linarith only [h1, h166, h168, hc02, hc34, hlam, hphi, ht23]
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
                    linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p170_1, u2elo3, u4ehi1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h1, hlam, p170_1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h1, h166, hc45, hlam, hphi, p170_1, u4ehi3]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h118, hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h0, hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h161, hlam, p170_1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p170_1, u4ehi3]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h163, hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h166, hc45, hlam, hphi, p170_1, u4ehi0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h166, hc45, hlam, hphi, p170_1, u4ehi1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h166, hc45, hlam, hphi, p170_1, u4ehi3]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h166, hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h0, h165, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p170_1, u2elo2, u4ehi1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h165, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p170_1, u2elo2, u4ehi1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h165, hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h168, hlam, p170_0]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p170_1, u4ehi1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [hc45, hlam, hphi, p170_1, u4ehi1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [h161, hc12, hc45, hlam, hphi, ht23, ht34, p170_1]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [hc45, hlam, hphi, p170_1, u4ehi3]
                  · have p170_0 := h170c.1
                    have p170_1 := h170c.2.1
                    have p170_2 := h170c.2.2.1
                    have p170_3 := h170c.2.2.2
                    linarith only [hlam, p170_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
              · linarith only [h0, h118, h196, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                · linarith only [h1, h196, h198, hc02, hc34, hlam, hphi, ht23]
                · rcases h4bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p200_1, u2elo3, u4ehi1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h1, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h1, h165, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h118, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h161, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h1, h165, hc01, hlam, hphi, ht0b, ht45, ht5b, p200_1, u4ehi0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h163, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p200_1, u2elo3, u4ehi0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h165, h198, hc45, hlam, hphi, p200_1, u4ehi1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h165, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h196, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h198, hc45, hlam, hphi, p200_1, u4ehi1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h198, hc45, hlam, hphi, p200_1, u4ehi1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h198, hc45, hlam, hphi, p200_1, u4ehi2]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h198, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p200_1, u4ehi1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hc45, hlam, hphi, p200_1, u4ehi1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hc45, hlam, hphi, p200_1, u4ehi3]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h226 | h226
    · rcases m.htr 0 4 5 (by decide) (by decide) with h227 | h227
      · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
        · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
          · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
            · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
              · linarith only [h226, h231, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
              · linarith only [h226, h227, h231, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
              · linarith only [h226, h234, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
              · linarith only [h0, h227, h228, h234, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
          · linarith only [h0, h227, h229, hlam]
        · linarith only [h226, h228, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
        · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
          · linarith only [h227, h239, h240, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
            · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
              · linarith only [h240, h243, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                · linarith only [h0, h240, h242, h245, hc01, hlam, hphi, ht12, u2elo2]
                · rcases h4bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h0, hlam, p247_1]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h0, h240, h242, hc45, hlam, hphi, p247_1, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h0, h240, hc45, hlam, hphi, p247_1, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h227, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h240, hc45, hlam, hphi, p247_1, u4ehi0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h240, h242, hc45, hlam, hphi, p247_1, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h240, hc45, hlam, hphi, p247_1, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h240, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h226, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h239, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1, u2elo3, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h243, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1, u2elo2, u4ehi0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p247_1, u2elo3, u4ehi1]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h242, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h245, hlam, p247_0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hc45, hlam, hphi, p247_1, u4ehi0]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p247_1]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [h242, hc45, hlam, hphi, p247_1, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hc45, hlam, hphi, p247_1, u4ehi3]
                  · have p247_0 := h247c.1
                    have p247_1 := h247c.2.1
                    have p247_2 := h247c.2.2.1
                    have p247_3 := h247c.2.2.2
                    linarith only [hlam, p247_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h273 | h273
              · linarith only [h226, h273, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h275 | h275
                · linarith only [h0, h240, h275, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases h4bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h0, hlam, p277_1]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h0, h240, hc45, hlam, hphi, p277_1, u4ehi2]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h0, h240, hc45, hlam, hphi, p277_1, u4ehi3]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h227, hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h240, hc45, hlam, hphi, p277_1, u4ehi0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h240, hc45, hlam, hphi, p277_1, u4ehi2]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h240, h242, hc23, hc45, hlam, hphi, ht34, p277_1]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h240, hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h226, hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h239, hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h242, hlam, p277_1]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h273, hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h226, h275, hc45, hlam, hphi, p277_1, u4ehi2]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h275, hc45, hlam, hphi, p277_1, u4ehi1]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h275, hc45, hlam, hphi, p277_1, u4ehi2]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h275, hlam, p277_0]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h226, hc45, hlam, hphi, p277_1, u4ehi2]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p277_1]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hc45, hlam, hphi, p277_1, u4ehi2]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hc45, hlam, hphi, p277_1, u4ehi3]
                  · have p277_0 := h277c.1
                    have p277_1 := h277c.2.1
                    have p277_2 := h277c.2.2.1
                    have p277_3 := h277c.2.2.2
                    linarith only [hlam, p277_0]
        · linarith only [h226, h239, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
      · rcases m.htr 1 2 4 (by decide) (by decide) with h305 | h305
        · linarith only [h226, h305, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
          · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
            · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
              · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                · linarith only [h308, h310, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                · linarith only [h0, h304, h305, h310, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · linarith only [h0, h304, h305, h309, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
              · rcases m.htr 3 4 5 (by decide) (by decide) with h315 | h315
                · rcases h4bigk with h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h0, hlam, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h226, hlam, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h0, h305, h308, hlam, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h0, h305, hlam, hphi, ht01, ht0b, ht12, ht5b, p316_1, u2elo3, u5ehi4]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h305, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p316_1, u2elo3, u4ehi0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h305, hlam, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h305, h308, hlam, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h305, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p316_1, u2elo3, u4ehi4]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h304, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p316_1, u2elo3, u4ehi4]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p316_1, u2elo3, u4ehi1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h308, hlam, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p316_1, u2elo3, u4ehi4]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h304, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p316_1, u4ehi4]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h0, h304, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p316_1, u4ehi4]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h305, hc12, hc34, hlam, hphi, ht23, p316_1]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    rcases p316_3 (m.d 0 4) (by simp) with h336 | h336
                    · linarith only [h0, h305, h308, h336, hlam]
                    · linarith only [h304, h336, hlam]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h304, hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h307, hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h314, hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [h315, hlam, p316_0]
                  · have p316_0 := h316c.1
                    have p316_1 := h316c.2.1
                    have p316_2 := h316c.2.2.1
                    have p316_3 := h316c.2.2.2
                    linarith only [hlam, p316_0]
                · linarith only [h0, h304, h305, h308, h315, hlam]
              · linarith only [h0, h304, h305, h314, hlam]
          · linarith only [h0, h304, h307, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
        · linarith only [h226, h347, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
          · linarith only [h304, h347, h349, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h351 | h351
            · rcases m.htr 2 4 5 (by decide) (by decide) with h352 | h352
              · linarith only [h349, h351, h352, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h354 | h354
                · linarith only [h347, h351, h352, h354, hc12, hlam, hphi, u2elo2]
                · rcases h4bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h0, hlam, p356_1]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h226, hlam, p356_1]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h0, h347, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p356_1, u2elo3, u4ehi3]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h304, hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h347, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p356_1, u2elo3, u4ehi0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h347, hlam, p356_1]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h347, h352, hc45, hlam, hphi, p356_1, u4ehi3]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h349, hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h352, hc45, hlam, hphi, p356_1, u4ehi0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h352, hc45, hlam, hphi, p356_1, u4ehi1]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h352, hc45, hlam, hphi, p356_1, u4ehi3]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h352, hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h351, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p356_1, u2elo2, u4ehi0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h0, h351, hc01, hlam, hphi, ht12, p356_1, u2elo2]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h351, hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h354, hlam, p356_0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hc45, hlam, hphi, p356_1, u4ehi0]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p356_1]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hc45, hlam, hphi, p356_1, u4ehi2]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hc45, hlam, hphi, p356_1, u4ehi3]
                  · have p356_0 := h356c.1
                    have p356_1 := h356c.2.1
                    have p356_2 := h356c.2.2.1
                    have p356_3 := h356c.2.2.2
                    linarith only [hlam, p356_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
              · linarith only [h304, h382, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
                · linarith only [h226, h382, h384, hc02, hc34, hlam, hphi, ht23]
                · rcases h4bigk with h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c | h386c
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h0, hlam, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h226, hlam, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h0, h347, h351, hlam, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h304, hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h347, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p386_1, u2elo3, u4ehi0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h347, hlam, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h347, h351, hlam, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h349, hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h351, h384, hc45, hlam, hphi, p386_1, u4ehi0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h351, h384, hc45, hlam, hphi, p386_1, u4ehi1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h351, hlam, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h382, hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h384, hc45, hlam, hphi, p386_1, u4ehi0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h0, h384, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h384, hc45, hlam, hphi, p386_1, u4ehi2]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h384, hlam, p386_0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hc45, hlam, hphi, p386_1, u4ehi0]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [h0, h347, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p386_1]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hc45, hlam, hphi, p386_1, u4ehi3]
                  · have p386_0 := h386c.1
                    have p386_1 := h386c.2.1
                    have p386_2 := h386c.2.2.1
                    have p386_3 := h386c.2.2.2
                    linarith only [hlam, p386_0]

theorem n7l_sAB2_M_IR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have h2ehi := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h11, h13, h6, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h10, h13, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h10, h12, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h11, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h10, h19, h3, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                            · linarith only [h10, h18, h21, h7, hc23, hlam, hphi, u2ehi3]
                            · rcases h4bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                rcases p23_3 (m.d 0 4) (by simp) with h25 | h25
                                · rcases p23_3 (m.d 1 4) (by simp) with h26 | h26
                                  · linarith only [h1, h26, hlam]
                                  · rcases p23_3 (m.d 2 4) (by simp) with h28 | h28
                                    · linarith only [h28, h3, hlam]
                                    · rcases p23_3 (m.d 3 4) (by simp) with h30 | h30
                                      · linarith only [h30, h4, hlam]
                                      · rcases p23_3 (m.d 4 5) (by simp) with h32 | h32
                                        · linarith only [h32, h5, hlam]
                                        · linarith only [h10, h32, hlam]
                                · linarith only [h1, h25, hlam]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                rcases p23_3 (m.d 0 4) (by simp) with h36 | h36
                                · rcases p23_3 (m.d 1 4) (by simp) with h37 | h37
                                  · linarith only [h1, h37, hlam]
                                  · linarith only [h37, h7, hlam]
                                · linarith only [h3, h36, hlam]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                rcases p23_3 (m.d 0 4) (by simp) with h41 | h41
                                · rcases p23_3 (m.d 1 4) (by simp) with h42 | h42
                                  · linarith only [h1, h42, hlam]
                                  · linarith only [h42, h9, hlam]
                                · linarith only [h4, h41, hlam]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, h10, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23_1, u2ehi3]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h1, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h10, hc45, hlam, hphi, ht23, ht34, p23_1, u2ehi3]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, h10, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi3]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h10, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h3, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h7, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi3]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h19, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h4, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h9, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h18, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h21, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h5, hlam, p23_0]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi1]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi2]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p23_1, u4ehi3]
                              · have p23_0 := h23c.1
                                have p23_1 := h23c.2.1
                                have p23_2 := h23c.2.2.1
                                have p23_3 := h23c.2.2.2
                                linarith only [hlam, p23_0]
                        · linarith only [h0, h18, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                        · linarith only [h6, h69, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                            · rcases h4bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h4, h7, h71, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h4, h71, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h4, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p73_1, u2ehi2]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                rcases p73_3 (m.d 0 4) (by simp) with h78 | h78
                                · rcases p73_3 (m.d 1 4) (by simp) with h79 | h79
                                  · linarith only [h1, h79, hlam]
                                  · linarith only [h68, h79, hlam]
                                · linarith only [h78, hlam, p73_0]
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
                                linarith only [h71, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p73_1, u4ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h9, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h3, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h7, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h69, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h4, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi2]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p73_1, u4ehi4]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h5, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h68, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h71, hlam, p73_0]
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
                            · linarith only [h3, h71, h72, h9, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h1, h68, h69, h71, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                        · linarith only [h105, h6, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h107, h6, h68, h9, hc24, hlam, hphi, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h0, h109, h4, h6, h68, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h109, h6, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h6, h8, hc25, hlam, hphi, u2ehi2]
                · linarith only [h6, h7, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                · linarith only [h114, h6, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                  · linarith only [h114, h116, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                            · linarith only [h0, h118, h122, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h119, h122, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h114, h119, h121, hlam]
                        · linarith only [h0, h120, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                          · linarith only [h119, h127, h128, h2, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h0, h114, h128, h4, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                        · linarith only [h127, h6, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                        · linarith only [h118, h132, h133, h2, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h133, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                        · linarith only [h118, h136, h6, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h136, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
              · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                      · linarith only [h1, h143, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                          · linarith only [h1, h140, h146, h5, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                            · linarith only [h139, h145, h148, h5, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases h4bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h140, h5, hc45, hlam, hphi, ht23, ht34, p150_1, u2ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h5, hc45, hlam, hphi, ht23, ht34, p150_1, u2ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h5, hc45, hlam, hphi, p150_1, u4ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h5, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h1, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u2ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h1, h5, hc45, hlam, hphi, p150_1, u4ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h143, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h3, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h140, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, ht0b, ht45, ht5b, p150_1, u4ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h146, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h4, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h142, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h145, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [h148, hlam, p150_0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hc45, hlam, hphi, p150_1, u4ehi0]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hc45, hlam, hphi, p150_1, u4ehi1]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p150_1, u2ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hc45, hlam, hphi, p150_1, u4ehi3]
                              · have p150_0 := h150c.1
                                have p150_1 := h150c.2.1
                                have p150_2 := h150c.2.2.1
                                have p150_3 := h150c.2.2.2
                                linarith only [hlam, p150_0]
                        · linarith only [h145, h4, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h139, h142, h4, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h139, h141, hc25, hlam, hphi, u2ehi2]
                · linarith only [h139, h140, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                · linarith only [h139, h180, hc23, hlam, hphi, u2ehi3]
                · linarith only [h180, h3, h5, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h183 | h183
            · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
              · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
                · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                    · linarith only [h0, h187, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h190 | h190
                        · linarith only [h0, h184, h190, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                            · rcases h4bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h185, h192, hc04, hlam, hphi, ht0b, ht45, ht5b, p194_1, u4ehi4]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h1, h192, hc01, hlam, hphi, ht0b, ht45, ht5b, p194_1, u4ehi4]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h4, hlam, p194_1]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                rcases p194_3 (m.d 0 4) (by simp) with h199 | h199
                                · rcases p194_3 (m.d 1 4) (by simp) with h200 | h200
                                  · linarith only [h1, h200, hlam]
                                  · linarith only [h189, h200, hlam]
                                · linarith only [h199, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h1, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h192, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p194_1, u4ehi4]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h187, hlam, p194_1]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p194_1, u4ehi4]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h3, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h185, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h190, hlam, p194_1]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h185, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p194_1, u4ehi4]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h3, hc34, hlam, hphi, ht23, p194_1, u2ehi3]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h186, h189, hc34, hlam, hphi, ht23, p194_1, u2ehi4]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [hc34, hlam, hphi, ht23, p194_1, u2ehi3]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                rcases p194_3 (m.d 0 4) (by simp) with h218 | h218
                                · linarith only [h218, h4, hlam]
                                · linarith only [h183, h218, hlam]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h183, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h189, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h192, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [h193, hlam, p194_0]
                              · have p194_0 := h194c.1
                                have p194_1 := h194c.2.1
                                have p194_2 := h194c.2.2.1
                                have p194_3 := h194c.2.2.2
                                linarith only [hlam, p194_0]
                            · linarith only [h1, h185, h192, h193, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h183, h192, h4, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h183, h185, h189, h4, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h184, h186, hc25, hlam, hphi, u2ehi2]
                · linarith only [h184, h185, hc24, hlam, hphi, u2ehi2]
              · linarith only [h184, h2, h4, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
              · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                    · linarith only [h0, h183, h235, h4, hc45, hlam, hphi, u4ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h1, h183, h237, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                        · linarith only [h0, h232, h239, h4, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h241 | h241
                          · linarith only [h1, h183, h233, h241, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                            · linarith only [h0, h183, h232, h243, h4, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h0, h232, h243, h4, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h232, h234, hc25, hlam, hphi, u2ehi2]
                · linarith only [h232, h233, hc24, hlam, hphi, u2ehi2]
              · linarith only [h2, h232, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h250 | h250
        · linarith only [h2, h250, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
          · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
            · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
              · linarith only [h0, h2, h254, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                · linarith only [h250, h254, h256, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                  · linarith only [h256, h258, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h263 | h263
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                            · linarith only [h0, h260, h264, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h261, h264, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h1, h250, h261, h263, hlam]
                        · linarith only [h2, h262, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2, h252, h253, h256, h261, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h2, h252, h254, h260, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h271 | h271
              · linarith only [h0, h2, h271, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                · linarith only [h250, h271, h273, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
                  · linarith only [h1, h253, h273, h275, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                      · linarith only [h1, h253, h278, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                          · linarith only [h1, h253, h273, h281, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h250, h281, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h2, h280, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h2, h252, h271, h277, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
            · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
              · linarith only [h0, h2, h287, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
                · linarith only [h250, h286, h287, h289, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h291 | h291
                  · linarith only [h289, h291, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h293 | h293
                    · linarith only [h0, h252, h293, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                        · linarith only [h0, h252, h287, h296, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h2, h296, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h252, h286, h289, h295, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
              · linarith only [h0, h2, h252, h286, h300, hc45, hlam, hphi, ht23, ht34, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                · linarith only [h300, h302, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                  · linarith only [h0, h252, h286, h300, h304, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                    · linarith only [h0, h252, h306, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                      · linarith only [h1, h286, h308, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                        · linarith only [h0, h252, h300, h310, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h2, h310, hc34, hlam, hphi, ht23, u2ehi0]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
      · rcases m.htr 0 2 4 (by decide) (by decide) with h314 | h314
        · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
          · linarith only [h0, h1, h315, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
            · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                    · linarith only [h0, h1, h315, h319, h321, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h318, h321, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h1, h318, h319, h320, hc25, hlam, hphi, u2ehi2]
                · linarith only [h318, h319, hc24, hlam, hphi, u2ehi2]
              · linarith only [h313, h315, h318, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
              · linarith only [h0, h1, h317, h327, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h313, h315, h327, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h313, h314, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h331 | h331
        · linarith only [h313, h331, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h333 | h333
          · linarith only [h0, h1, h333, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
            · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
              · linarith only [h0, h313, h333, h336, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
                · linarith only [h331, h335, h336, h338, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h1, h336, h338, hc24, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
              · linarith only [h0, h1, h335, h341, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h1, h335, h341, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
    · rcases m.htr 0 2 3 (by decide) (by decide) with h345 | h345
      · rcases m.htr 0 2 4 (by decide) (by decide) with h346 | h346
        · rcases m.htr 0 3 4 (by decide) (by decide) with h347 | h347
          · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
            · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
              · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 2 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h353 | h353
                      · linarith only [h0, h344, h349, h353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h344, h348, h349, h353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h344, h348, h352, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h0, h344, h349, h350, h351, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h344, h349, h350, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h344, h345, h348, h349, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
              · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
                · rcases m.htr 1 2 5 (by decide) (by decide) with h362 | h362
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h364 | h364
                      · linarith only [h344, h348, h364, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                          · linarith only [h344, h348, h361, h367, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h369 | h369
                            · linarith only [h344, h348, h361, h369, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h4bigk with h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h348, h361, hc45, hlam, hphi, ht23, ht34, p371_1, u2ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h348, hc45, hlam, hphi, ht23, ht34, p371_1, u2ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h348, hc45, hlam, hphi, p371_1, u4ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h348, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h344, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h0, h344, h360, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p371_1, u2ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h0, h344, h360, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p371_1, u4ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h364, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h346, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h361, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h346, hc02, hlam, hphi, ht0b, ht45, ht5b, p371_1, u4ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h367, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h347, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h363, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h366, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h369, hlam, p371_0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hc45, hlam, hphi, p371_1, u4ehi0]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [h361, hc45, hlam, hphi, ht23, ht34, p371_1, u2ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p371_1, u2ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hc45, hlam, hphi, p371_1, u4ehi3]
                              · have p371_0 := h371c.1
                                have p371_1 := h371c.2.1
                                have p371_2 := h371c.2.2.1
                                have p371_3 := h371c.2.2.2
                                linarith only [hlam, p371_0]
                        · linarith only [h347, h348, h366, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h347, h348, h363, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h344, h360, h361, h362, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h344, h360, h361, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h344, h345, h360, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h0, h344, h347, hlam]
        · linarith only [h345, h346, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
        · linarith only [h345, h404, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h406 | h406
          · rcases m.htr 0 4 5 (by decide) (by decide) with h407 | h407
            · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
              · rcases m.htr 1 2 4 (by decide) (by decide) with h409 | h409
                · linarith only [h0, h344, h345, h404, h408, h409, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h344, h345, h408, h409, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
                · linarith only [h408, h412, hc23, hlam, hphi, u2ehi3]
                · linarith only [h0, h344, h408, h412, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
              · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                · linarith only [h0, h344, h404, h416, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h344, h345, h415, h416, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                · linarith only [h415, h419, hc23, hlam, hphi, u2ehi3]
                · linarith only [h0, h344, h415, h419, hc23, hlam, hphi, u2ehi1]
          · linarith only [h0, h344, h406, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h423 | h423
      · rcases m.htr 0 2 4 (by decide) (by decide) with h424 | h424
        · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
          · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
            · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
              · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
                · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h434 | h434
                            · linarith only [h423, h432, h434, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h427, h432, h433, h434, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h437 | h437
                            · linarith only [h433, h437, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h4bigk with h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h344, hlam, p439_1]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                rcases p439_3 (m.d 0 4) (by simp) with h442 | h442
                                · rcases p439_3 (m.d 1 4) (by simp) with h443 | h443
                                  · rcases p439_3 (m.d 2 4) (by simp) with h444 | h444
                                    · linarith only [h424, h444, hlam]
                                    · rcases p439_3 (m.d 3 4) (by simp) with h446 | h446
                                      · linarith only [h425, h446, hlam]
                                      · rcases p439_3 (m.d 4 5) (by simp) with h448 | h448
                                        · linarith only [h426, h448, hlam]
                                        · linarith only [h433, h448, hlam]
                                  · linarith only [h428, h443, hlam]
                                · linarith only [h424, h442, hlam]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                rcases p439_3 (m.d 0 4) (by simp) with h453 | h453
                                · rcases p439_3 (m.d 1 4) (by simp) with h454 | h454
                                  · rcases p439_3 (m.d 2 4) (by simp) with h455 | h455
                                    · linarith only [h424, h455, hlam]
                                    · linarith only [h432, h455, hlam]
                                  · linarith only [h430, h454, hlam]
                                · linarith only [h425, h453, hlam]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h433, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p439_1, u2ehi3]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h426, h433, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p439_1, u2ehi3]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                rcases p439_3 (m.d 0 4) (by simp) with h463 | h463
                                · linarith only [h344, h463, hlam]
                                · linarith only [h424, h463, hlam]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                rcases p439_3 (m.d 0 4) (by simp) with h466 | h466
                                · linarith only [h344, h466, hlam]
                                · linarith only [h425, h466, hlam]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h427, h430, h433, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p439_1, u2ehi3]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h424, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h428, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h426, h433, hc04, hlam, hphi, ht0b, ht45, ht5b, p439_1, u4ehi3]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h433, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h425, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h430, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h432, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h437, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h426, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h431, hlam, p439_0]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h426, hc04, hlam, hphi, ht0b, ht45, ht5b, p439_1, u4ehi2]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [h344, h426, h427, h430, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p439_1, u4ehi3]
                              · have p439_0 := h439c.1
                                have p439_1 := h439c.2.1
                                have p439_2 := h439c.2.2.1
                                have p439_3 := h439c.2.2.2
                                linarith only [hlam, p439_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h485 | h485
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h486 | h486
                            · rcases h4bigk with h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h344, hlam, p487_1]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h485, hc04, hlam, hphi, ht0b, ht5b, p487_1, u5ehi4]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h0, h425, h427, h432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p487_1, u2ehi2]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                rcases p487_3 (m.d 0 4) (by simp) with h492 | h492
                                · rcases p487_3 (m.d 1 4) (by simp) with h493 | h493
                                  · rcases p487_3 (m.d 2 4) (by simp) with h494 | h494
                                    · linarith only [h424, h494, hlam]
                                    · linarith only [h485, h494, hlam]
                                  · linarith only [h431, h493, hlam]
                                · linarith only [h492, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h424, h427, h430, h485, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p487_1, u4ehi4]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h427, h430, h485, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p487_1, u4ehi4]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h427, h430, h432, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p487_1, u2ehi2]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                rcases p487_3 (m.d 0 4) (by simp) with h503 | h503
                                · linarith only [h344, h503, hlam]
                                · linarith only [h426, h503, hlam]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h424, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h428, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h432, hlam, p487_1]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h424, hc02, hlam, hphi, ht0b, ht45, ht5b, p487_1, u4ehi4]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h425, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h430, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [hc34, hlam, hphi, ht23, p487_1, u2ehi3]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h0, h425, h427, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p487_1, u4ehi4]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h426, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h431, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h485, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [h486, hlam, p487_0]
                              · have p487_0 := h487c.1
                                have p487_1 := h487c.2.1
                                have p487_2 := h487c.2.2.1
                                have p487_3 := h487c.2.2.2
                                linarith only [hlam, p487_0]
                            · linarith only [h432, h485, h486, hc24, hlam, hphi, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                            · linarith only [h0, h425, h427, h432, h485, h522, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h426, h432, h522, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h344, h426, h431, hlam]
                    · linarith only [h0, h425, h430, hlam]
                  · linarith only [h427, h429, hc25, hlam, hphi, u2ehi2]
                · linarith only [h427, h428, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h423, h427, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
              · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
                · rcases m.htr 1 2 5 (by decide) (by decide) with h532 | h532
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h534 | h534
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h536 | h536
                          · linarith only [h424, h426, h536, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h538 | h538
                            · linarith only [h424, h426, h538, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h4bigk with h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h344, hlam, p540_1]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h426, h530, h533, h534, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p540_1, u2ehi3]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h426, h530, h533, h534, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p540_1, u4ehi3]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h426, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                rcases p540_3 (m.d 0 4) (by simp) with h546 | h546
                                · linarith only [h344, h546, hlam]
                                · rcases p540_3 (m.d 1 4) (by simp) with h548 | h548
                                  · rcases p540_3 (m.d 2 4) (by simp) with h549 | h549
                                    · linarith only [h531, h549, hlam]
                                    · rcases p540_3 (m.d 3 4) (by simp) with h551 | h551
                                      · linarith only [h533, h551, hlam]
                                      · rcases p540_3 (m.d 4 5) (by simp) with h553 | h553
                                        · linarith only [h534, h553, hlam]
                                        · linarith only [h426, h553, hlam]
                                  · linarith only [h344, h548, hlam]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                rcases p540_3 (m.d 0 4) (by simp) with h558 | h558
                                · linarith only [h344, h558, hlam]
                                · linarith only [h424, h558, hlam]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                rcases p540_3 (m.d 0 4) (by simp) with h561 | h561
                                · linarith only [h344, h561, hlam]
                                · linarith only [h425, h561, hlam]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h426, h530, h533, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p540_1, u4ehi0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h424, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h531, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h424, h426, hc45, hlam, hphi, p540_1, u4ehi3]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h536, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h425, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h533, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h535, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h538, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [hc45, hlam, hphi, p540_1, u4ehi0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h534, hlam, p540_0]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h530, h533, h534, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p540_1, u2ehi3]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [h530, h533, h534, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p540_1, u4ehi3]
                              · have p540_0 := h540c.1
                                have p540_1 := h540c.2.1
                                have p540_2 := h540c.2.2.1
                                have p540_3 := h540c.2.2.2
                                linarith only [hlam, p540_0]
                        · linarith only [h425, h426, h530, h533, h534, h535, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h582 | h582
                          · linarith only [h344, h534, h582, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                            · linarith only [h344, h424, h534, h581, h584, hc23, hlam, hphi, u2ehi3]
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
                                linarith only [h344, hlam, p586_1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h344, h534, hc45, hlam, hphi, ht23, ht34, p586_1, u2ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h344, h534, hc45, hlam, hphi, p586_1, u4ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h426, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h534, hc45, hlam, hphi, p586_1, u4ehi0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h534, hc45, hlam, hphi, ht23, ht34, p586_1, u2ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h534, hc45, hlam, hphi, p586_1, u4ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h534, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h424, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h531, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h344, h424, h534, hc45, hlam, hphi, p586_1, u4ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h582, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h425, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h533, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h581, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [h584, hlam, p586_0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hc45, hlam, hphi, p586_1, u4ehi0]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hc45, hlam, hphi, p586_1, u4ehi1]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hc45, hlam, hphi, ht23, ht34, p586_1, u2ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hc45, hlam, hphi, p586_1, u4ehi3]
                              · have p586_0 := h586c.1
                                have p586_1 := h586c.2.1
                                have p586_2 := h586c.2.2.1
                                have p586_3 := h586c.2.2.2
                                linarith only [hlam, p586_0]
                        · linarith only [h425, h426, h581, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h425, h533, hlam]
                  · linarith only [h530, h532, hc25, hlam, hphi, u2ehi2]
                · linarith only [h530, h531, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h423, h530, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
            · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
              · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
                · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                        · linarith only [h423, h425, h623, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h625 | h625
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h626 | h626
                            · rcases h4bigk with h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h344, hlam, p627_1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h625, hc04, hlam, hphi, ht0b, ht45, ht5b, p627_1, u4ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h425, hlam, p627_1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h425, h618, h621, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p627_1, u4ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h424, h625, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p627_1, u4ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h619, h625, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p627_1, u4ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h423, h425, h618, h621, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p627_1, u2ehi2]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                rcases p627_3 (m.d 0 4) (by simp) with h637 | h637
                                · linarith only [h344, h637, hlam]
                                · linarith only [h617, h637, hlam]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h424, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h619, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h623, hlam, p627_1]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h424, hc02, hlam, hphi, ht0b, ht45, ht5b, p627_1, u4ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h424, hc34, hlam, hphi, ht23, p627_1, u2ehi3]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h621, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h618, h621, h625, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p627_1, u2ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h618, h621, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p627_1, u4ehi4]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h617, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h622, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h625, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [h626, hlam, p627_0]
                              · have p627_0 := h627c.1
                                have p627_1 := h627c.2.1
                                have p627_2 := h627c.2.2.1
                                have p627_3 := h627c.2.2.2
                                linarith only [hlam, p627_0]
                            · linarith only [h424, h425, h625, h626, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h425, h617, h618, h621, h625, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h425, h617, h618, h621, h622, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h658 | h658
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h659 | h659
                        · linarith only [h0, h621, h659, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h661 | h661
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
                            · rcases h4bigk with h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h344, hlam, p663_1]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h661, hc04, hlam, hphi, ht0b, ht45, ht5b, p663_1, u4ehi4]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h425, hlam, p663_1]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                rcases p663_3 (m.d 0 4) (by simp) with h668 | h668
                                · rcases p663_3 (m.d 1 4) (by simp) with h669 | h669
                                  · rcases p663_3 (m.d 2 4) (by simp) with h670 | h670
                                    · linarith only [h424, h670, hlam]
                                    · linarith only [h661, h670, hlam]
                                  · linarith only [h658, h669, hlam]
                                · linarith only [h668, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h424, h621, h661, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p663_1, u4ehi4]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h621, h661, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p663_1, u4ehi4]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h621, hlam, p663_1]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                rcases p663_3 (m.d 0 4) (by simp) with h679 | h679
                                · linarith only [h344, h679, hlam]
                                · linarith only [h617, h679, hlam]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h424, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h619, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h659, hlam, p663_1]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h424, hc02, hlam, hphi, ht0b, ht45, ht5b, p663_1, u4ehi4]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h424, hc34, hlam, hphi, ht23, p663_1, u2ehi3]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h344, hc01, hc34, hlam, hphi, ht12, ht23, p663_1]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [hc34, hlam, hphi, ht23, p663_1, u2ehi3]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                rcases p663_3 (m.d 0 4) (by simp) with h691 | h691
                                · linarith only [h425, h691, hlam]
                                · linarith only [h617, h691, hlam]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h617, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h658, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h661, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [h662, hlam, p663_0]
                              · have p663_0 := h663c.1
                                have p663_1 := h663c.2.1
                                have p663_2 := h663c.2.2.1
                                have p663_3 := h663c.2.2.2
                                linarith only [hlam, p663_0]
                            · linarith only [h424, h661, h662, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h344, h617, h621, h661, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h344, h617, h658, hlam]
                  · linarith only [h618, h620, hc25, hlam, hphi, u2ehi2]
                · linarith only [h618, h619, hc24, hlam, hphi, u2ehi2]
              · linarith only [h423, h425, h618, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h705 | h705
              · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
                · rcases m.htr 1 2 5 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h708 | h708
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h709 | h709
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                        · linarith only [h423, h425, h617, h705, h708, h709, h710, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h712 | h712
                          · linarith only [h424, h617, h712, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h714 | h714
                            · linarith only [h423, h425, h617, h714, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h423, h425, h705, h708, h709, h714, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h423, h425, h708, h709, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                      · linarith only [h424, h617, h708, h718, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h720 | h720
                        · linarith only [h0, h423, h708, h718, h720, hc45, hlam, hphi, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h722 | h722
                          · linarith only [h0, h708, h718, h722, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                            · linarith only [h0, h423, h708, h718, h724, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h423, h425, h724, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h705, h707, hc25, hlam, hphi, u2ehi2]
                · linarith only [h705, h706, hc24, hlam, hphi, u2ehi2]
              · linarith only [h423, h425, h705, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h423, h424, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h731 | h731
        · linarith only [h423, h731, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h733 | h733
          · rcases m.htr 0 4 5 (by decide) (by decide) with h734 | h734
            · rcases m.htr 1 2 3 (by decide) (by decide) with h735 | h735
              · rcases m.htr 1 2 4 (by decide) (by decide) with h736 | h736
                · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h742 | h742
                            · linarith only [h423, h733, h735, h742, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h423, h733, h734, h735, h742, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h423, h731, h733, h734, h735, h741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h423, h740, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h344, h423, h733, h734, h739, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h423, h733, h735, h738, hc01, hc12, hlam, hphi]
                  · linarith only [h423, h733, h735, h737, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h423, h735, h736, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h751 | h751
                · linarith only [h735, h751, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h751, h753, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h756 | h756
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h757 | h757
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h758 | h758
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h759 | h759
                            · rcases h4bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h344, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h731, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h759, hc04, hlam, hphi, ht0b, ht45, ht5b, p760_1, u4ehi4]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                rcases p760_3 (m.d 0 4) (by simp) with h765 | h765
                                · rcases p760_3 (m.d 1 4) (by simp) with h766 | h766
                                  · rcases p760_3 (m.d 2 4) (by simp) with h767 | h767
                                    · rcases p760_3 (m.d 3 4) (by simp) with h768 | h768
                                      · linarith only [h733, h768, hlam]
                                      · linarith only [h759, h768, hlam]
                                    · linarith only [h758, h767, hlam]
                                  · linarith only [h756, h766, hlam]
                                · linarith only [h765, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h731, h735, h755, hc23, hlam, hphi, p760_1, u2ehi0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h751, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h735, h755, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p760_1, u4ehi4]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                rcases p760_3 (m.d 0 4) (by simp) with h778 | h778
                                · linarith only [h344, h778, hlam]
                                · linarith only [h734, h778, hlam]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h733, h757, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p760_1, u4ehi4]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h344, h757, hc01, hc23, hlam, hphi, ht12, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h757, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p760_1, u4ehi4]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                rcases p760_3 (m.d 0 4) (by simp) with h785 | h785
                                · linarith only [h731, h785, hlam]
                                · linarith only [h734, h785, hlam]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h733, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h755, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h757, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h733, hc03, hlam, hphi, ht0b, ht45, ht5b, p760_1, u4ehi4]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h734, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h756, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h758, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h759, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                            · rcases h4bigk with h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h344, hlam, p798_1]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h731, hlam, p798_1]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                rcases p798_3 (m.d 0 4) (by simp) with h802 | h802
                                · rcases p798_3 (m.d 1 4) (by simp) with h803 | h803
                                  · rcases p798_3 (m.d 2 4) (by simp) with h804 | h804
                                    · rcases p798_3 (m.d 3 4) (by simp) with h805 | h805
                                      · linarith only [h733, h805, hlam]
                                      · rcases p798_3 (m.d 4 5) (by simp) with h807 | h807
                                        · linarith only [h734, h807, hlam]
                                        · linarith only [h759, h807, hlam]
                                    · linarith only [h757, h804, hlam]
                                  · linarith only [h755, h803, hlam]
                                · linarith only [h733, h802, hlam]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h0, h733, h735, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p798_1, u4ehi3]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h731, h751, h757, hc23, hlam, hphi, p798_1, u2ehi0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h751, hlam, p798_1]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                rcases p798_3 (m.d 0 4) (by simp) with h817 | h817
                                · linarith only [h344, h817, hlam]
                                · linarith only [h733, h817, hlam]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h751, h757, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p798_1, u4ehi3]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h734, h757, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p798_1, u4ehi3]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h344, h757, hc01, hc23, hlam, hphi, ht12, p798_1]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                rcases p798_3 (m.d 0 4) (by simp) with h824 | h824
                                · linarith only [h731, h824, hlam]
                                · linarith only [h733, h824, hlam]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h757, h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p798_1, u4ehi3]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h733, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h755, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h757, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h759, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h734, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h756, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h758, hlam, p798_0]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [h734, hc04, hlam, hphi, ht0b, ht45, ht5b, p798_1, u4ehi3]
                              · have p798_0 := h798c.1
                                have p798_1 := h798c.2.1
                                have p798_2 := h798c.2.2.1
                                have p798_3 := h798c.2.2.2
                                linarith only [hlam, p798_0]
                          · linarith only [h0, h733, h734, h735, h758, hc23, hlam, hphi, u2ehi3]
                        · linarith only [h423, h757, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h344, h734, h756, hlam]
                    · linarith only [h0, h733, h755, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
              · rcases m.htr 1 2 4 (by decide) (by decide) with h843 | h843
                · rcases m.htr 1 2 5 (by decide) (by decide) with h844 | h844
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h845 | h845
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h846 | h846
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h847 | h847
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                          · linarith only [h731, h734, h842, h847, h848, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h731, h845, h846, h848, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h423, h847, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h731, h843, h846, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h423, h733, h842, h845, hlam]
                  · linarith only [h423, h733, h842, h844, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h423, h842, h843, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h856 | h856
                · linarith only [h842, h856, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h858 | h858
                  · linarith only [h856, h858, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h860 | h860
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                      · linarith only [h731, h734, h842, h860, h861, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h863 | h863
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h864 | h864
                          · linarith only [h856, h861, h863, h864, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h731, h864, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h0, h733, h842, h863, hlam]
                    · linarith only [h0, h733, h860, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h869 | h869
            · rcases m.htr 1 2 3 (by decide) (by decide) with h870 | h870
              · rcases m.htr 1 2 4 (by decide) (by decide) with h871 | h871
                · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h873 | h873
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h874 | h874
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h875 | h875
                        · linarith only [h423, h733, h870, h875, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h423, h873, h875, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h344, h869, h874, hlam]
                    · linarith only [h423, h870, h873, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h731, h869, h871, h872, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h423, h870, h871, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h882 | h882
                · linarith only [h870, h882, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h884 | h884
                  · linarith only [h882, h884, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                    · linarith only [h423, h733, h870, h886, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                        · linarith only [h870, h886, h889, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h423, h889, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h344, h869, h888, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h893 | h893
              · rcases m.htr 1 2 4 (by decide) (by decide) with h894 | h894
                · rcases m.htr 1 2 5 (by decide) (by decide) with h895 | h895
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h896 | h896
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h897 | h897
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h898 | h898
                        · linarith only [h423, h733, h898, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h423, h898, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h731, h894, h897, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h423, h893, h896, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h423, h893, h895, hc25, hlam, hphi, u2ehi0]
                · linarith only [h423, h893, h894, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h905 | h905
                · linarith only [h893, h905, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
                  · linarith only [h905, h907, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
                    · linarith only [h423, h733, h893, h909, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                      · linarith only [h731, h869, h909, h911, hc34, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                        · linarith only [h423, h733, h913, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h423, h913, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
