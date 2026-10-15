import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LI_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
                              · linarith only [h0, h14, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h12, h14, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h13, h8, hc14, hlam, hphi, u4elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                              · linarith only [h0, h19, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                                · linarith only [h0, h10, h21, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h18, h21, hc24, hlam, hphi, u4elo1]
                            · linarith only [h18, h8, hc14, hlam, hphi, u4elo0]
                        · linarith only [h11, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h10, h9, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                            · linarith only [h32, h8, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                              · linarith only [h0, h28, h34, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1, h31, h34, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h31, h7, h8, hc13, hlam, hphi, ht34, u4elo4]
                        · linarith only [h30, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h28, h29, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h28, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                          · linarith only [h1, h45, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                              · linarith only [h1, h42, h48, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                                · linarith only [h0, h43, h50, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h41, h50, h7, hc24, hlam, hphi, u4elo3]
                            · linarith only [h41, h47, h7, hc14, hlam, hphi, u4elo3]
                        · linarith only [h44, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h42, h43, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h4, h42, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                          · linarith only [h1, h41, h60, h7, hc34, hlam, hphi, u4elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                            · linarith only [h41, h62, h7, hc03, hlam, hphi, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                              · linarith only [h1, h57, h64, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                                · linarith only [h0, h41, h58, h66, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                                  · linarith only [h41, h68, h7, hc03, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h1, h57, h68, h7, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h59, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h57, h58, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h4, h57, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h74 | h74
                · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
                  · linarith only [h5, h6, h75, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                        · linarith only [h0, h6, h79, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                            · linarith only [h2, h75, h82, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                              · linarith only [h0, h6, h77, h84, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                              · linarith only [h4, h6, h74, h84, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · linarith only [h4, h6, h74, h81, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h5, h6, h78, hc12, hlam, hphi, u2elo4]
                    · linarith only [h4, h6, h77, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
                  · linarith only [h5, h6, h90, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h0, h6, h94, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                          · linarith only [h1, h74, h90, h96, hc34, hlam, hphi, u4elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                            · linarith only [h2, h90, h98, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                              · linarith only [h0, h100, h74, h92, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                                · linarith only [h102, h90, hc04, hlam, hphi, u4elo2]
                                · linarith only [h0, h100, h102, h6, h93, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h5, h6, h93, hc12, hlam, hphi, u2elo4]
                    · linarith only [h4, h6, h92, hc12, hlam, hphi, u2elo4]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 0 2 5 (by decide) (by decide) with h109 | h109
              · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
                · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                    · linarith only [h108, h112, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h119 | h119
                                · linarith only [h0, h114, h119, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h117, h119, h2, hc24, hlam, hphi, u4elo0]
                              · linarith only [h118, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h108, h111, h117, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h110, h112, h115, h116, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h109, h114, h115, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h108, h114, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
                    · linarith only [h127, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h111, h132, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h135 | h135
                                · linarith only [h111, h129, h135, h2, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h137 | h137
                                  · linarith only [h111, h129, h134, h137, h2, hlam]
                                  · rcases h0bigk with h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h0, h130, h134, h135, hc34, hlam, hphi, ht0b, ht45, ht5b, p139_1, u0elo0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h1, h127, h130, h134, h135, hc34, hlam, hphi, ht0b, ht45, ht5b, p139_1, u0elo0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 1) (by simp) with h143 | h143
                                      · rcases p139_3 (m.d 0 2) (by simp) with h144 | h144
                                        · linarith only [h0, h144, hlam]
                                        · linarith only [h108, h144, hlam]
                                      · linarith only [h143, h2, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 1) (by simp) with h148 | h148
                                      · rcases p139_3 (m.d 0 2) (by simp) with h149 | h149
                                        · linarith only [h0, h149, hlam]
                                        · linarith only [h109, h149, hlam]
                                      · linarith only [h148, h3, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h0, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h4, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h129, h134, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p139_1, u2elo2]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p139_1, u2elo2]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h1, hlam, p139_1]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h0, h130, h134, h135, hc34, hlam, hphi, ht0b, ht45, ht5b, p139_1, u0elo2]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 1) (by simp) with h161 | h161
                                      · rcases p139_3 (m.d 0 2) (by simp) with h162 | h162
                                        · linarith only [h162, h4, hlam]
                                        · linarith only [h108, h162, hlam]
                                      · linarith only [h161, h2, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      rcases p139_3 (m.d 0 1) (by simp) with h166 | h166
                                      · rcases p139_3 (m.d 0 2) (by simp) with h167 | h167
                                        · linarith only [h167, h4, hlam]
                                        · linarith only [h109, h167, hlam]
                                      · linarith only [h166, h3, hlam]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h2, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h108, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h110, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h111, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h3, hlam, p139_0]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h109, hlam, p139_1]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h1, h127, h130, h134, h135, hc34, hlam, hphi, ht0b, ht45, ht5b, p139_1, u0elo4]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [h109, h129, h134, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p139_1, u2elo2]
                                    · have p139_0 := h139c.1
                                      have p139_1 := h139c.2.1
                                      have p139_2 := h139c.2.2.1
                                      have p139_3 := h139c.2.2.2
                                      linarith only [hlam, p139_0]
                              · linarith only [h134, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h110, h111, h127, h129, h131, hc24, hlam, hphi, u4elo4]
                        · linarith only [h109, h129, h130, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h108, h129, h4, hc12, hlam, hphi, u2elo2]
                · linarith only [h108, h110, h4, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h186 | h186
                · rcases m.htr 0 4 5 (by decide) (by decide) with h187 | h187
                  · linarith only [h108, h109, h187, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
                    · linarith only [h0, h189, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                        · linarith only [h0, h109, h192, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                            · linarith only [h187, h195, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                                · linarith only [h0, h187, h191, h198, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h0, h109, h191, h198, hc24, hlam, hphi, u4elo4]
                              · linarith only [h0, h191, h197, h4, hc24, hlam, hphi, u4elo3]
                          · linarith only [h186, h189, h191, h194, hc24, hlam, hphi, u4elo0]
                      · linarith only [h108, h191, h4, hc12, hlam, hphi, u2elo2]
                · linarith only [h108, h186, h4, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 0 3 4 (by decide) (by decide) with h206 | h206
                · rcases m.htr 0 4 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                    · linarith only [h0, h108, h208, hc23, hlam, hphi, ht34, u4elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                      · linarith only [h0, h108, h210, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h214 | h214
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h217 | h217
                                  · linarith only [h1, h213, h217, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h207, h217, hc34, hlam, hphi, u4elo0]
                                · linarith only [h0, h108, h212, h214, h216, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h212, h215, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h207, h214, hc14, hlam, hphi, u4elo0]
                          · linarith only [h206, h208, h212, h213, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h108, h205, h212, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h108, h205, h207, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
                    · linarith only [h0, h227, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h229 | h229
                      · linarith only [h0, h206, h229, h4, hc24, hlam, hphi, u4elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                          · linarith only [h1, h206, h232, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                              · linarith only [h0, h206, h231, h235, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · linarith only [h0, h231, h235, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h226, h227, h231, h232, h234, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h108, h205, h231, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h205, h206, h226, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
                · rcases m.htr 0 4 5 (by decide) (by decide) with h242 | h242
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                    · linarith only [h0, h243, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
                      · linarith only [h0, h108, h245, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
                        · linarith only [h0, h205, h247, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h249 | h249
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h253 | h253
                                  · linarith only [h1, h249, h253, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · linarith only [h242, h253, hc34, hlam, hphi, u4elo0]
                                · linarith only [h1, h108, h249, h250, h252, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h251, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h242, h245, h250, hc12, hlam, hphi, ht23, ht34, u4elo0]
                          · linarith only [h241, h243, h249, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                    · linarith only [h0, h260, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                      · linarith only [h0, h108, h242, h262, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                        · linarith only [h0, h205, h264, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
                            · linarith only [h108, h242, h267, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                                · linarith only [h0, h108, h242, h269, h270, hc12, hlam, hphi, u2elo2]
                                · linarith only [h0, h108, h270, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h266, h269, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h241, h242, h266, hc13, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h275 | h275
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                    · linarith only [h0, h276, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
                      · linarith only [h0, h108, h241, h278, h4, hc04, hlam, hphi, u4elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                        · linarith only [h0, h205, h280, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
                          · linarith only [h1, h241, h282, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                              · linarith only [h0, h241, h285, h4, hc12, hlam, hphi, u2elo2]
                              · linarith only [h0, h285, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                            · linarith only [h275, h284, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
                    · linarith only [h0, h289, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
                      · linarith only [h0, h108, h291, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                        · linarith only [h0, h205, h293, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                          · linarith only [h1, h241, h275, h295, hc34, hlam, hphi, u4elo4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                            · linarith only [h241, h275, h297, h4, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                              · linarith only [h0, h241, h299, h4, hc12, hlam, hphi, u2elo2]
                              · linarith only [h0, h299, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h302 | h302
          · rcases m.htr 0 2 4 (by decide) (by decide) with h303 | h303
            · rcases m.htr 0 2 5 (by decide) (by decide) with h304 | h304
              · linarith only [h0, h3, h304, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
                · rcases m.htr 0 4 5 (by decide) (by decide) with h307 | h307
                  · linarith only [h2, h3, h307, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h309 | h309
                    · linarith only [h0, h3, h307, h309, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h302, h304, h309, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                  · linarith only [h2, h3, h312, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
                    · linarith only [h0, h3, h312, h314, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h302, h304, h314, hc12, hlam, hphi, u2elo4]
            · linarith only [h302, h303, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
            · rcases m.htr 0 2 5 (by decide) (by decide) with h319 | h319
              · linarith only [h0, h3, h302, h319, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 4 5 (by decide) (by decide) with h322 | h322
                  · linarith only [h2, h3, h322, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
                    · linarith only [h302, h324, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h326 | h326
                      · linarith only [h1, h3, h322, h324, h326, hc24, hlam, hphi, u4elo4]
                      · linarith only [h302, h318, h326, hc12, hlam, hphi, u2elo2]
                · linarith only [h302, h318, h321, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h330 | h330
              · linarith only [h1, h3, h318, h330, hc13, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
                · rcases m.htr 0 4 5 (by decide) (by decide) with h333 | h333
                  · linarith only [h1, h3, h332, h333, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
                    · linarith only [h0, h318, h333, h335, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                      · linarith only [h1, h3, h333, h335, h337, hc24, hlam, hphi, u4elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                        · linarith only [h1, h3, h330, h335, h339, hlam]
                        · linarith only [h1, h3, h335, h339, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
                  · linarith only [h2, h3, h342, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
                    · linarith only [h0, h302, h344, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h346 | h346
                      · linarith only [h0, h318, h346, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                        · linarith only [h0, h330, h348, hlam]
                        · linarith only [h0, h3, h348, hc12, hlam, hphi, u2elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h352 | h352
      · rcases m.htr 0 1 5 (by decide) (by decide) with h353 | h353
        · rcases m.htr 0 2 3 (by decide) (by decide) with h354 | h354
          · linarith only [h0, h1, h354, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
            · rcases m.htr 0 2 5 (by decide) (by decide) with h357 | h357
              · rcases m.htr 0 3 4 (by decide) (by decide) with h358 | h358
                · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                    · linarith only [h0, h354, h360, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1, h360, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                    · linarith only [h0, h1, h354, h363, hlam]
                    · linarith only [h0, h1, h363, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h358, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h367 | h367
                · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h356, h357, h368, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                    · linarith only [h0, h354, h370, hlam]
                    · linarith only [h0, h1, h370, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h367, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h374 | h374
              · rcases m.htr 0 3 4 (by decide) (by decide) with h375 | h375
                · rcases m.htr 0 4 5 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
                    · linarith only [h0, h356, h377, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1, h377, hc12, hlam, hphi, u2elo2]
                  · linarith only [h356, h374, h376, hlam]
                · linarith only [h0, h1, h375, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h382 | h382
                · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                    · linarith only [h0, h356, h384, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1, h384, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h387 | h387
                    · linarith only [h0, h356, h387, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1, h387, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h382, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h391 | h391
          · linarith only [h0, h1, h391, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
            · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
              · linarith only [h0, h353, h394, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h396 | h396
                · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
                  · linarith only [h352, h353, h397, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h399 | h399
                    · linarith only [h0, h391, h399, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1, h399, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h396, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h403 | h403
              · linarith only [h0, h353, h393, h403, hc12, hlam, hphi, ht23, ht34, u4elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
                · rcases m.htr 0 4 5 (by decide) (by decide) with h406 | h406
                  · linarith only [h352, h353, h406, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                    · linarith only [h0, h393, h406, h408, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1, h408, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h405, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h352, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h413 | h413
    · rcases m.htr 0 1 4 (by decide) (by decide) with h414 | h414
      · rcases m.htr 0 1 5 (by decide) (by decide) with h415 | h415
        · rcases m.htr 0 2 3 (by decide) (by decide) with h416 | h416
          · rcases m.htr 0 2 4 (by decide) (by decide) with h417 | h417
            · rcases m.htr 0 2 5 (by decide) (by decide) with h418 | h418
              · rcases m.htr 0 3 4 (by decide) (by decide) with h419 | h419
                · rcases m.htr 0 4 5 (by decide) (by decide) with h420 | h420
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h423 | h423
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h424 | h424
                          · linarith only [h0, h413, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h0, h413, h419, h421, h424, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h423, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h414, h417, h422, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h413, h419, h421, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                          · linarith only [h0, h413, h433, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h0, h413, h419, h433, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h432, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h413, h430, h431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h430, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h439 | h439
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h442 | h442
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h443 | h443
                          · linarith only [h413, h419, h443, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
                            · linarith only [h0, h414, h445, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h0, h414, h439, h445, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h442, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h413, h440, h441, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h413, h440, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                          · linarith only [h0, h413, h454, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h456 | h456
                            · linarith only [h414, h439, h456, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h458 | h458
                              · linarith only [h0, h416, h419, h458, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h460 | h460
                                · linarith only [h414, h439, h452, h460, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h462 | h462
                                  · linarith only [h439, h462, hc04, hlam, hphi, u4elo3]
                                  · linarith only [h413, h419, h451, h462, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h0, h453, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h452, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h413, h416, h451, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h415, h418, hlam]
            · linarith only [h0, h413, h417, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h413, h416, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h471 | h471
          · rcases m.htr 0 2 4 (by decide) (by decide) with h472 | h472
            · rcases m.htr 0 2 5 (by decide) (by decide) with h473 | h473
              · rcases m.htr 0 3 4 (by decide) (by decide) with h474 | h474
                · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
                  · linarith only [h413, h415, h474, h475, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
                          · linarith only [h413, h415, h479, h480, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h413, h415, h474, h477, h479, h480, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h473, h479, hc12, hlam, hphi, u2elo0]
                      · linarith only [h0, h413, h477, h478, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h477, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h486 | h486
                  · linarith only [h414, h415, h486, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h489 | h489
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                          · linarith only [h413, h415, h490, h491, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h493 | h493
                            · linarith only [h414, h415, h474, h486, h490, h493, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h414, h415, h493, hc14, hlam, hphi, u4elo4]
                        · linarith only [h0, h413, h473, h488, h490, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h413, h488, h489, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h413, h488, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
                · rcases m.htr 0 4 5 (by decide) (by decide) with h500 | h500
                  · linarith only [h0, h414, h473, h500, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h503 | h503
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h504 | h504
                        · linarith only [h0, h473, h504, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h413, h502, h504, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h413, h502, h503, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h413, h502, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h509 | h509
                  · linarith only [h414, h415, h509, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h513 | h513
                        · linarith only [h0, h473, h513, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h413, h511, h513, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h413, h511, h512, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h413, h511, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h413, h472, hc13, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h413, h471, hlam]
      · linarith only [h413, h414, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h521 | h521
      · rcases m.htr 0 1 5 (by decide) (by decide) with h522 | h522
        · rcases m.htr 0 2 3 (by decide) (by decide) with h523 | h523
          · rcases m.htr 0 2 4 (by decide) (by decide) with h524 | h524
            · rcases m.htr 0 2 5 (by decide) (by decide) with h525 | h525
              · rcases m.htr 0 3 4 (by decide) (by decide) with h526 | h526
                · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h529 | h529
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h530 | h530
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h532 | h532
                            · linarith only [h413, h521, h528, h532, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h527, h532, hc14, hlam, hphi, u4elo0]
                          · linarith only [h413, h521, h529, h531, hc24, hlam, hphi, u4elo3]
                        · linarith only [h413, h521, h528, h529, h530, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h413, h521, h528, h529, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h523, h528, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h540 | h540
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h541 | h541
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                            · linarith only [h521, h527, h543, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                                · linarith only [h521, h527, h540, h546, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h548 | h548
                                  · linarith only [h521, h527, h540, h545, h548, hlam]
                                  · rcases h0bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h0, hlam, p550_1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h413, hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h413, h539, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p550_1, u2elo1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h413, h539, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p550_1, u2elo1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p550_1, u2elo1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h0, h413, h521, h540, h545, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p550_1, u2elo1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      rcases p550_3 (m.d 0 1) (by simp) with h559 | h559
                                      · linarith only [h0, h559, hlam]
                                      · linarith only [h521, h559, hlam]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      rcases p550_3 (m.d 0 1) (by simp) with h562 | h562
                                      · linarith only [h0, h562, hlam]
                                      · linarith only [h522, h562, hlam]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h522, h540, h543, h545, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1, u0elo2]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h523, hlam, p550_1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      rcases p550_3 (m.d 0 1) (by simp) with h568 | h568
                                      · linarith only [h413, h568, hlam]
                                      · linarith only [h521, h568, hlam]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      rcases p550_3 (m.d 0 1) (by simp) with h571 | h571
                                      · linarith only [h413, h571, hlam]
                                      · linarith only [h522, h571, hlam]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h521, hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h524, hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h526, hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h527, hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h522, hlam, p550_0]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h525, hlam, p550_1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h413, h522, h540, h543, h545, hc34, hlam, hphi, ht0b, ht45, ht5b, p550_1, u0elo4]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [h0, h521, h522, h540, h545, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p550_1, u2elo1]
                                    · have p550_0 := h550c.1
                                      have p550_1 := h550c.2.1
                                      have p550_2 := h550c.2.2.1
                                      have p550_3 := h550c.2.2.2
                                      linarith only [hlam, p550_0]
                              · linarith only [h526, h527, h545, hc23, hlam, hphi, ht34, u4elo4]
                          · linarith only [h413, h526, h527, h542, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h521, h540, h541, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h413, h539, h540, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h523, h539, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h413, h521, h526, hc14, hlam, hphi, u4elo3]
              · linarith only [h413, h522, h523, h525, hlam]
            · linarith only [h413, h521, h523, h524, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h592 | h592
            · rcases m.htr 0 2 5 (by decide) (by decide) with h593 | h593
              · rcases m.htr 0 3 4 (by decide) (by decide) with h594 | h594
                · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h596 | h596
                    · linarith only [h523, h596, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h521, h596, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h599 | h599
                    · linarith only [h0, h521, h523, h599, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h521, h599, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h0, h521, h523, h594, hc14, hlam, hphi, u4elo3]
              · linarith only [h0, h522, h593, hlam]
            · linarith only [h0, h521, h592, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h605 | h605
          · rcases m.htr 0 2 4 (by decide) (by decide) with h606 | h606
            · rcases m.htr 0 2 5 (by decide) (by decide) with h607 | h607
              · rcases m.htr 0 3 4 (by decide) (by decide) with h608 | h608
                · rcases m.htr 0 4 5 (by decide) (by decide) with h609 | h609
                  · linarith only [h521, h522, h609, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h611 | h611
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h612 | h612
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h613 | h613
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h614 | h614
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h615 | h615
                            · linarith only [h521, h609, h615, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h521, h522, h615, hc14, hlam, hphi, u4elo4]
                          · linarith only [h413, h521, h612, h614, hc24, hlam, hphi, u4elo3]
                        · linarith only [h413, h521, h607, h611, h612, h613, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h521, h612, hc14, hlam, hphi, u4elo2]
                    · linarith only [h0, h521, h605, h611, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h413, h521, h608, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h623 | h623
                · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
                  · linarith only [h0, h521, h607, h624, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h626 | h626
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h627 | h627
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h628 | h628
                        · linarith only [h413, h605, h607, h628, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h521, h627, h628, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h413, h521, h626, h627, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h521, h626, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h413, h521, h623, hc14, hlam, hphi, u4elo3]
            · linarith only [h605, h606, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h635 | h635
            · rcases m.htr 0 2 5 (by decide) (by decide) with h636 | h636
              · rcases m.htr 0 3 4 (by decide) (by decide) with h637 | h637
                · rcases m.htr 0 4 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h521, h522, h638, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
                    · linarith only [h521, h522, h605, h636, h640, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h521, h640, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h521, h522, h605, h636, h637, hc14, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h644 | h644
                · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                  · linarith only [h0, h521, h636, h645, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
                    · linarith only [h0, h605, h647, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h521, h647, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h0, h521, h605, h644, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h521, h635, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h652 | h652
        · rcases m.htr 0 2 3 (by decide) (by decide) with h653 | h653
          · rcases m.htr 0 2 4 (by decide) (by decide) with h654 | h654
            · rcases m.htr 0 2 5 (by decide) (by decide) with h655 | h655
              · rcases m.htr 0 3 4 (by decide) (by decide) with h656 | h656
                · rcases m.htr 0 4 5 (by decide) (by decide) with h657 | h657
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h660 | h660
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h661 | h661
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h662 | h662
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h663 | h663
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h665 | h665
                                  · linarith only [h653, h663, h665, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h521, h652, h660, h664, h665, hc34, hlam, hphi, u4elo1]
                                · linarith only [h657, h664, hc24, hlam, hphi, u4elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h669 | h669
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h670 | h670
                                  · rcases h0bigk with h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, hlam, p671_1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h413, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h521, hlam, p671_1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h521, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p671_1, u4elo1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p671_1, u2elo1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h656, h663, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p671_1, u2elo1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h521, h652, h660, h669, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p671_1, u2elo1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      rcases p671_3 (m.d 0 1) (by simp) with h681 | h681
                                      · linarith only [h0, h681, hlam]
                                      · linarith only [h652, h681, hlam]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h652, h660, h669, hc45, hlam, hphi, ht0b, ht5b, p671_1, u0elo2]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h653, hlam, p671_1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h521, h652, h653, h656, h660, h663, h669, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p671_1, u2elo1, u4elo1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      rcases p671_3 (m.d 0 1) (by simp) with h688 | h688
                                      · linarith only [h413, h688, hlam]
                                      · linarith only [h652, h688, hlam]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h652, h660, h669, hc45, hlam, hphi, ht0b, ht5b, p671_1, u0elo3]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h654, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h656, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      rcases p671_3 (m.d 0 1) (by simp) with h695 | h695
                                      · linarith only [h521, h695, hlam]
                                      · linarith only [h652, h695, hlam]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h652, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h655, hlam, p671_1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h413, h652, hc15, hlam, hphi, ht0b, ht5b, p671_1, u0elo4]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h657, hlam, p671_1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                  · linarith only [h521, h652, h660, h663, h669, h670, hc23, hlam, hphi, ht34, u4elo1]
                                · linarith only [h521, h657, h669, hc24, hlam, hphi, u4elo1]
                            · linarith only [h521, h652, h657, h662, hlam]
                          · linarith only [h413, h656, h661, hlam]
                        · linarith only [h0, h660, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h653, h656, h659, hc34, hlam, hphi, u4elo2]
                    · linarith only [h0, h658, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h521, h652, h657, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h714 | h714
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h715 | h715
                          · linarith only [h413, h652, h656, h712, h714, h715, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h413, h652, h714, h715, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                        · linarith only [h0, h714, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h413, h652, h654, h712, h713, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h652, h712, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h413, h652, h656, h711, hlam]
              · linarith only [h0, h652, h655, hlam]
            · linarith only [h653, h654, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h724 | h724
            · rcases m.htr 0 2 5 (by decide) (by decide) with h725 | h725
              · rcases m.htr 0 3 4 (by decide) (by decide) with h726 | h726
                · rcases m.htr 0 4 5 (by decide) (by decide) with h727 | h727
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h728 | h728
                    · linarith only [h653, h728, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h652, h728, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h521, h652, h727, hlam]
                · linarith only [h653, h724, h726, hc24, hlam, hphi, u4elo3]
              · linarith only [h521, h652, h724, h725, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h734 | h734
              · rcases m.htr 0 3 4 (by decide) (by decide) with h735 | h735
                · rcases m.htr 0 4 5 (by decide) (by decide) with h736 | h736
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
                    · linarith only [h653, h737, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h652, h737, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h652, h724, h736, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h741 | h741
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
                    · linarith only [h0, h652, h653, h742, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h652, h742, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h652, h653, h735, h741, hlam]
              · linarith only [h0, h652, h734, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h747 | h747
          · rcases m.htr 0 2 4 (by decide) (by decide) with h748 | h748
            · rcases m.htr 0 2 5 (by decide) (by decide) with h749 | h749
              · rcases m.htr 0 3 4 (by decide) (by decide) with h750 | h750
                · rcases m.htr 0 4 5 (by decide) (by decide) with h751 | h751
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h753 | h753
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h756 | h756
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h757 | h757
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h758 | h758
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h759 | h759
                                  · linarith only [h747, h757, h759, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h751, h759, hc34, hlam, hphi, u4elo0]
                                · linarith only [h521, h751, h758, hc24, hlam, hphi, u4elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h763 | h763
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h764 | h764
                                  · rcases h0bigk with h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, hlam, p765_1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h413, hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h521, hlam, p765_1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h652, hlam, p765_1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h750, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h521, hc01, hlam, hphi, ht12, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h652, hc01, hlam, hphi, ht12, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h747, hc01, hlam, hphi, ht12, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h747, hlam, p765_1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h747, h748, h763, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h652, h747, hc01, hlam, hphi, ht12, p765_1, u2elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p765_1, u4elo0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h748, hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h750, hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [hlam, p765_0]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h521, h652, h747, h750, h757, hc01, hc23, hlam, hphi, ht12, ht34, p765_1, u2elo1, u4elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h0, h652, h747, h750, h756, h757, hc01, hc23, hlam, hphi, ht12, ht34, p765_1, u2elo1, u4elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h749, hlam, p765_1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h652, h750, h756, h757, hc23, hlam, hphi, ht34, p765_1, u4elo1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [h751, hlam, p765_1]
                                    · have p765_0 := h765c.1
                                      have p765_1 := h765c.2.1
                                      have p765_2 := h765c.2.2.1
                                      have p765_3 := h765c.2.2.2
                                      linarith only [hlam, p765_0]
                                  · linarith only [h757, h763, h764, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                · linarith only [h521, h751, h763, hc24, hlam, hphi, u4elo1]
                            · linarith only [h521, h751, h756, hlam]
                          · linarith only [h413, h750, h755, hlam]
                        · linarith only [h0, h749, h754, hlam]
                      · linarith only [h0, h747, h750, h753, hc34, hlam, hphi, u4elo2]
                    · linarith only [h0, h747, h752, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h799 | h799
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h800 | h800
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h801 | h801
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h802 | h802
                            · linarith only [h751, h802, hc04, hlam, hphi, u4elo1]
                            · linarith only [h521, h802, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h413, h750, h801, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                        · linarith only [h0, h749, h800, hlam]
                      · linarith only [h0, h748, h751, h799, hc02, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h747, h798, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h811 | h811
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h812 | h812
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h813 | h813
                          · linarith only [h413, h750, h810, h813, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h413, h813, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h812, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h748, h811, hlam]
                    · linarith only [h0, h810, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h820 | h820
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h821 | h821
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h822 | h822
                          · linarith only [h413, h750, h819, h822, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h413, h822, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h749, h821, hc12, hlam, hphi, u2elo0]
                      · linarith only [h0, h748, h809, h820, hc02, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h747, h819, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h828 | h828
                · rcases m.htr 0 4 5 (by decide) (by decide) with h829 | h829
                  · linarith only [h748, h749, h829, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h832 | h832
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h833 | h833
                        · linarith only [h749, h833, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h833, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h413, h748, h831, h832, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h747, h749, h831, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h838 | h838
                  · linarith only [h748, h749, h838, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h840 | h840
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h841 | h841
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h842 | h842
                        · linarith only [h749, h842, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h842, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h413, h748, h840, h841, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h840, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h747, h748, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h848 | h848
            · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
              · rcases m.htr 0 3 4 (by decide) (by decide) with h850 | h850
                · rcases m.htr 0 4 5 (by decide) (by decide) with h851 | h851
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h852 | h852
                    · linarith only [h747, h848, h852, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h852, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h855 | h855
                    · linarith only [h747, h848, h855, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h855, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h747, h848, h850, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h859 | h859
                · rcases m.htr 0 4 5 (by decide) (by decide) with h860 | h860
                  · linarith only [h848, h849, h860, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                    · linarith only [h747, h848, h862, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h862, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h747, h848, h859, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h866 | h866
              · rcases m.htr 0 3 4 (by decide) (by decide) with h867 | h867
                · rcases m.htr 0 4 5 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h869 | h869
                    · linarith only [h747, h869, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h869, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h848, h866, h868, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h873 | h873
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
                    · linarith only [h747, h866, h874, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h874, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h747, h866, h867, h873, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h878 | h878
                · rcases m.htr 0 4 5 (by decide) (by decide) with h879 | h879
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h880 | h880
                    · linarith only [h747, h880, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h880, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h883 | h883
                    · linarith only [h0, h747, h883, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h883, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
                    · linarith only [h0, h747, h887, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h887, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h890 | h890
                    · linarith only [h0, h747, h890, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h890, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
