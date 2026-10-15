import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_25_L_I_L_0_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h3, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h3, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                        · linarith only [h15, h3, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h15, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h12, h4, h5, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
                · linarith only [h19, h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h21, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h24, h5, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                        · linarith only [h1, h26, h3, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h19, h2, h23, h26, h28, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h0, h21, h23, h30, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                              · linarith only [h3, h30, h32, h5, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  rcases p34_3 (m.d 0 1) (by simp) with h36 | h36
                                  · rcases p34_3 (m.d 0 2) (by simp) with h37 | h37
                                    · linarith only [h0, h37, hlam]
                                    · rcases p34_3 (m.d 0 3) (by simp) with h39 | h39
                                      · linarith only [h1, h39, hlam]
                                      · rcases p34_3 (m.d 0 4) (by simp) with h41 | h41
                                        · linarith only [h4, h41, hlam, p34_1]
                                        · rcases p34_3 (m.d 0 5) (by simp) with h43 | h43
                                          · linarith only [h2, h43, hlam]
                                          · linarith only [h43, h5, hlam]
                                  · linarith only [h0, h36, hlam]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  rcases p34_3 (m.d 0 1) (by simp) with h47 | h47
                                  · rcases p34_3 (m.d 0 2) (by simp) with h48 | h48
                                    · linarith only [h0, h48, hlam]
                                    · linarith only [h3, h48, hlam]
                                  · linarith only [h1, h47, hlam]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  rcases p34_3 (m.d 0 1) (by simp) with h52 | h52
                                  · rcases p34_3 (m.d 0 2) (by simp) with h53 | h53
                                    · linarith only [h0, h53, hlam]
                                    · linarith only [h4, h53, hlam]
                                  · linarith only [h52, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h0, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p34_1, u2elo4]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p34_1, u2elo4]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h5, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h1, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h3, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h7, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h19, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h0, h23, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h4, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h1, h4, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p34_1, u2elo4]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h21, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h2, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h5, hc02, hlam, hphi, p34_1, u2elo4]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  rcases p34_3 (m.d 0 1) (by simp) with h75 | h75
                                  · rcases p34_3 (m.d 0 2) (by simp) with h76 | h76
                                    · linarith only [h5, h76, hlam]
                                    · linarith only [h3, h76, hlam]
                                  · linarith only [h1, h75, hlam]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  rcases p34_3 (m.d 0 1) (by simp) with h80 | h80
                                  · rcases p34_3 (m.d 0 2) (by simp) with h81 | h81
                                    · linarith only [h5, h81, hlam]
                                    · linarith only [h4, h81, hlam]
                                  · linarith only [h2, h5, h80, hlam, hphi, ht01, ht0b, ht12, ht5b, p34_1, u2elo4, u5ehi1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                    · linarith only [h23, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h87 | h87
            · linarith only [h4, h87, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h89 | h89
              · linarith only [h3, h4, h89, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
                · linarith only [h3, h4, h91, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                  · linarith only [h4, h93, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                    · linarith only [h4, h95, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                      · linarith only [h0, h4, h87, h97, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                        · linarith only [h3, h4, h89, h99, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                          · linarith only [h101, h2, h91, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                            · linarith only [h103, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                            · linarith only [h103, h3, h4, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
            · linarith only [h107, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
              · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
                · linarith only [h110, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                  · linarith only [h106, h112, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h107, h115, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                          · linarith only [h118, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                            · linarith only [h0, h112, h114, h118, h120, h3, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                              · linarith only [h0, h114, h117, h118, h120, h122, h3, hlam]
                              · linarith only [h0, h114, h118, h122, h3, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h109, h114, h117, h3, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h106, h114, h3, hc12, hlam, hphi, u2elo2]
              · linarith only [h106, h109, h3, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h128 | h128
            · linarith only [h128, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
              · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                · linarith only [h131, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h133 | h133
                  · linarith only [h106, h133, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
                    · linarith only [h106, h135, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                      · linarith only [h0, h128, h137, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h139 | h139
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                          · linarith only [h106, h130, h131, h140, hc02, hlam, hphi, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                            · linarith only [h133, h142, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                              · linarith only [h130, h144, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h0bigk with h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  rcases p146_3 (m.d 0 1) (by simp) with h148 | h148
                                  · rcases p146_3 (m.d 0 2) (by simp) with h149 | h149
                                    · linarith only [h0, h149, hlam]
                                    · rcases p146_3 (m.d 0 3) (by simp) with h151 | h151
                                      · linarith only [h1, h151, hlam]
                                      · linarith only [h151, h3, hlam]
                                  · linarith only [h0, h148, hlam]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  rcases p146_3 (m.d 0 1) (by simp) with h155 | h155
                                  · rcases p146_3 (m.d 0 2) (by simp) with h156 | h156
                                    · linarith only [h0, h156, hlam]
                                    · rcases p146_3 (m.d 0 3) (by simp) with h158 | h158
                                      · linarith only [h1, h158, hlam]
                                      · rcases p146_3 (m.d 0 4) (by simp) with h160 | h160
                                        · linarith only [h106, h160, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
                                        · rcases p146_3 (m.d 0 5) (by simp) with h162 | h162
                                          · linarith only [h162, h2, hlam]
                                          · linarith only [h131, h162, hlam]
                                  · linarith only [h1, h155, hlam]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  rcases p146_3 (m.d 0 1) (by simp) with h166 | h166
                                  · rcases p146_3 (m.d 0 2) (by simp) with h167 | h167
                                    · linarith only [h0, h167, hlam]
                                    · rcases p146_3 (m.d 0 3) (by simp) with h169 | h169
                                      · linarith only [h1, h169, hlam]
                                      · linarith only [h130, h169, hlam]
                                  · linarith only [h166, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p146_1, u5ehi1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h3, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h106, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h128, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h1, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p146_1, u2elo2]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h140, h144, h3, hc04, hc45, hlam, hphi, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h131, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h2, hc04, hlam, hphi, ht0b, ht5b, p146_1, u5ehi1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h106, hc12, hlam, hphi, p146_1, u2elo3]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h130, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h133, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h2, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h128, hc12, hlam, hphi, p146_1, u2elo4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h128, h130, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p146_1, u2elo4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h106, h128, hc12, hlam, hphi, p146_1, u2elo4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                        · linarith only [h130, h139, h3, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h195 | h195
                · linarith only [h130, h195, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h106, h197, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                    · linarith only [h0, h106, h199, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                      · linarith only [h0, h106, h128, h201, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                        · linarith only [h130, h203, h3, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                          · linarith only [h195, h205, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                            · linarith only [h207, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h209 | h209
                              · linarith only [h0, h203, h207, h209, h3, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h203, h209, h3, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h212 | h212
        · rcases m.htr 0 2 4 (by decide) (by decide) with h213 | h213
          · rcases m.htr 0 2 5 (by decide) (by decide) with h214 | h214
            · linarith only [h214, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h216 | h216
              · rcases m.htr 0 3 5 (by decide) (by decide) with h217 | h217
                · linarith only [h1, h2, h214, h217, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h213, h214, h219, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h214, h222, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h2, h222, hc12, hlam, hphi, u2elo4]
                    · linarith only [h213, h221, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h226 | h226
                · linarith only [h213, h214, h216, h226, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
                  · linarith only [h213, h214, h228, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                      · linarith only [h214, h231, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h2, h230, h231, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h213, h230, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
            · linarith only [h213, h235, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
              · linarith only [h212, h213, h237, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h239 | h239
                · linarith only [h212, h213, h239, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                  · linarith only [h213, h241, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                    · linarith only [h213, h243, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                      · linarith only [h0, h2, h235, h245, hlam]
                      · linarith only [h0, h2, h245, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
          · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
            · linarith only [h212, h249, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h251 | h251
              · rcases m.htr 0 3 5 (by decide) (by decide) with h252 | h252
                · linarith only [h1, h2, h252, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h254 | h254
                  · linarith only [h212, h248, h254, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                      · linarith only [h249, h257, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                      · linarith only [h0, h2, h256, h257, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h212, h248, h256, hc12, hlam, hphi, u2elo2]
              · linarith only [h212, h248, h251, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
            · linarith only [h212, h262, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
              · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
                · linarith only [h1, h2, h265, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                  · linarith only [h248, h267, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                    · linarith only [h248, h269, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                      · linarith only [h0, h262, h271, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi0]
                      · linarith only [h0, h2, h271, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h274 | h274
                · linarith only [h1, h2, h274, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
                  · linarith only [h248, h276, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
                    · linarith only [h0, h2, h248, h262, h278, hc02, hlam, hphi, u2elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                      · linarith only [h0, h262, h280, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi0]
                      · linarith only [h0, h2, h280, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h283 | h283
      · linarith only [h1, h283, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h285 | h285
        · linarith only [h0, h1, h285, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h287 | h287
          · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
            · linarith only [h285, h288, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h290 | h290
              · rcases m.htr 0 3 5 (by decide) (by decide) with h291 | h291
                · linarith only [h285, h291, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
                  · linarith only [h285, h287, h293, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h288, h296, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h0, h283, h295, h296, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h285, h287, h295, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h285, h287, h290, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h301 | h301
            · linarith only [h285, h301, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h303 | h303
              · rcases m.htr 0 3 5 (by decide) (by decide) with h304 | h304
                · linarith only [h285, h304, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h306 | h306
                  · linarith only [h287, h306, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
                    · linarith only [h287, h308, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h301, h310, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h0, h283, h310, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h313 | h313
                · linarith only [h303, h313, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h315 | h315
                  · linarith only [h287, h315, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                    · linarith only [h0, h1, h303, h315, h317, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                      · linarith only [h0, h1, h303, h315, h319, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · linarith only [h0, h283, h319, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h322 | h322
    · rcases m.htr 0 1 5 (by decide) (by decide) with h323 | h323
      · linarith only [h0, h323, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h325 | h325
        · rcases m.htr 0 2 4 (by decide) (by decide) with h326 | h326
          · rcases m.htr 0 2 5 (by decide) (by decide) with h327 | h327
            · linarith only [h327, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 0 3 5 (by decide) (by decide) with h330 | h330
                · linarith only [h0, h322, h327, h330, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h0, h322, h327, h329, h332, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h0, h327, h335, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h322, h329, h335, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h0, h322, h326, h329, h334, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                · linarith only [h329, h339, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h341 | h341
                  · linarith only [h326, h327, h341, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                      · linarith only [h0, h322, h327, h344, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h322, h344, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h322, h326, h343, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h348 | h348
            · linarith only [h326, h348, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h350 | h350
              · linarith only [h0, h322, h326, h350, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h352 | h352
                · linarith only [h350, h352, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
                  · linarith only [h326, h354, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                    · linarith only [h0, h322, h326, h356, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h322, h356, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
        · linarith only [h0, h322, h325, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h360 | h360
      · linarith only [h0, h360, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h362 | h362
        · rcases m.htr 0 2 4 (by decide) (by decide) with h363 | h363
          · rcases m.htr 0 2 5 (by decide) (by decide) with h364 | h364
            · linarith only [h0, h364, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h366 | h366
              · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
                · linarith only [h362, h364, h367, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
                  · linarith only [h362, h364, h366, h369, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
                      · linarith only [h322, h362, h364, h372, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h372, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h371, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h376 | h376
                · linarith only [h366, h376, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
                  · linarith only [h363, h364, h378, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
                      · linarith only [h364, h381, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h381, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h380, hc01, hlam, hphi, ht12, u2elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h385 | h385
            · linarith only [h385, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h387 | h387
              · linarith only [h362, h363, h387, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h389 | h389
                · linarith only [h362, h363, h389, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
                  · linarith only [h363, h391, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h393 | h393
                    · linarith only [h363, h393, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h393, hc01, hlam, hphi, ht12, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h396 | h396
          · rcases m.htr 0 2 5 (by decide) (by decide) with h397 | h397
            · linarith only [h362, h397, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h399 | h399
              · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
                · linarith only [h362, h400, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
                  · linarith only [h362, h396, h402, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                      · linarith only [h397, h405, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                      · linarith only [h0, h405, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h362, h396, h404, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h362, h396, h399, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h410 | h410
            · linarith only [h362, h410, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h412 | h412
              · rcases m.htr 0 3 5 (by decide) (by decide) with h413 | h413
                · linarith only [h362, h413, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
                  · linarith only [h396, h415, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h417 | h417
                    · linarith only [h396, h417, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h417, hc01, hlam, hphi, ht12, u2elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h420 | h420
                · linarith only [h412, h420, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h422 | h422
                  · linarith only [h396, h422, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h424 | h424
                    · linarith only [h0, h396, h424, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h424, hc01, hlam, hphi, ht12, u2elo3]

theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
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
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h0, h11, h13, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h12, hc14, hlam, hphi, ht45, u5elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                            · linarith only [h0, h18, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                              · linarith only [h11, h20, h4, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h20, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h17, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h10, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h4, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h7, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                        · linarith only [h1, h32, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                            · linarith only [h1, h29, h35, h6, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                              · linarith only [h0, h30, h35, h37, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                              · linarith only [h37, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h34, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h29, h30, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h29, h4, hc12, hlam, hphi, u2elo0]
                · linarith only [h28, hc04, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
              · linarith only [h4, h45, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                    · linarith only [h49, h5, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                        · linarith only [h1, h45, h52, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                            · linarith only [h0, h45, h48, h5, h55, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                              · linarith only [h0, h48, h5, h57, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                              · linarith only [h57, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h48, h49, h54, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h48, h51, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h4, h48, h5, hc12, hlam, hphi, u2elo3]
                · linarith only [h47, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
            · rcases m.htr 0 3 4 (by decide) (by decide) with h65 | h65
              · rcases m.htr 0 4 5 (by decide) (by decide) with h66 | h66
                · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                  · linarith only [h4, h64, h67, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                                · linarith only [h0, h4, h69, h75, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                · linarith only [h73, h75, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h4, h69, h73, h74, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h0, h4, h65, h69, h73, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h72, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h4, h64, h65, h67, h71, hc12, hlam, hphi, u2elo2]
                      · linarith only [h69, h70, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h4, h64, h69, hc12, hlam, hphi, u2elo2]
                · linarith only [h66, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h4, h64, h65, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h86 | h86
              · rcases m.htr 0 4 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
                  · linarith only [h4, h88, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h0, h64, h90, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                                  · linarith only [h1, h93, h98, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                  · linarith only [h98, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h2, h64, h92, h94, h96, h97, hc04, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h64, h95, h96, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h4, h86, h92, h95, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h94, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h4, h86, h88, h92, h93, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · linarith only [h92, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h87, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                  · linarith only [h0, h109, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
                    · linarith only [h0, h111, h64, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                        · linarith only [h0, h113, h114, h4, h86, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                            · linarith only [h0, h113, h117, h4, h86, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                                  · rcases h4bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h109, h113, h114, h119, h121, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p122_1, u1elo0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h64, hlam, p122_1]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h86, hlam, p122_1]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      rcases p122_3 (m.d 0 4) (by simp) with h127 | h127
                                      · rcases p122_3 (m.d 1 4) (by simp) with h128 | h128
                                        · linarith only [h128, h2, hlam]
                                        · linarith only [h116, h128, hlam]
                                      · linarith only [h127, hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h2, hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h111, hlam, p122_1]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h114, hlam, p122_1]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p122_1, u1elo0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h0, h113, h119, h121, h64, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p122_1, u2elo3]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h111, h113, h119, h121, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p122_1, u2elo3]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h117, hlam, p122_1]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      rcases p122_3 (m.d 0 4) (by simp) with h141 | h141
                                      · linarith only [h141, h64, hlam]
                                      · linarith only [h108, h141, hlam]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      rcases p122_3 (m.d 0 4) (by simp) with h144 | h144
                                      · linarith only [h144, h86, hlam]
                                      · rcases p122_3 (m.d 1 4) (by simp) with h146 | h146
                                        · linarith only [h114, h146, hlam]
                                        · rcases p122_3 (m.d 2 4) (by simp) with h148 | h148
                                          · linarith only [h117, h148, hlam]
                                          · linarith only [h148, h64, hlam]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      rcases p122_3 (m.d 0 4) (by simp) with h151 | h151
                                      · linarith only [h151, h86, hlam]
                                      · linarith only [h151, h2, hlam]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h0, h113, h119, h121, h64, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p122_1]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h0, h113, h117, h119, h121, h4, hlam, p122_2]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h108, hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h116, hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h120, hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [h121, hlam, p122_0]
                                    · have p122_0 := h122c.1
                                      have p122_1 := h122c.2.1
                                      have p122_2 := h122c.2.2.1
                                      have p122_3 := h122c.2.2.2
                                      linarith only [hlam, p122_0]
                                  · linarith only [h117, h121, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h113, h116, h117, h119, h120, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                              · linarith only [h0, h113, h119, h4, hc25, hlam, hphi, u5elo3]
                          · linarith only [h116, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h113, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h108, h4, h86, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h169 | h169
        · rcases m.htr 0 2 3 (by decide) (by decide) with h170 | h170
          · rcases m.htr 0 2 4 (by decide) (by decide) with h171 | h171
            · linarith only [h0, h171, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h173 | h173
              · linarith only [h1, h173, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                  · linarith only [h0, h176, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h170, h176, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h175, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h180 | h180
            · linarith only [h1, h170, h180, h2, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
              · linarith only [h1, h182, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h184 | h184
                · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
                  · linarith only [h0, h170, h185, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h187 | h187
                    · linarith only [h0, h180, h187, h2, hlam]
                    · linarith only [h1, h185, h187, h2, hc12, hlam, hphi, u2elo3]
                · linarith only [h184, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h0, h169, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h192 | h192
      · rcases m.htr 0 1 5 (by decide) (by decide) with h193 | h193
        · rcases m.htr 0 2 3 (by decide) (by decide) with h194 | h194
          · linarith only [h0, h1, h194, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h196 | h196
            · rcases m.htr 0 3 4 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 4 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                  · linarith only [h0, h1, h194, h199, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1, h199, hc12, hlam, hphi, u2elo2]
                · linarith only [h198, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h1, h192, h197, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h204 | h204
              · rcases m.htr 0 4 5 (by decide) (by decide) with h205 | h205
                · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
                  · linarith only [h0, h1, h206, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1, h206, hc12, hlam, hphi, u2elo2]
                · linarith only [h205, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h1, h192, h204, hlam]
        · linarith only [h0, h193, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
          · linarith only [h0, h1, h213, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h215 | h215
            · linarith only [h0, h192, h215, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
                · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
                  · linarith only [h0, h1, h213, h219, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1, h219, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h192, h218, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
                · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                  · linarith only [h0, h1, h224, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1, h224, hc12, hlam, hphi, u2elo2]
                · linarith only [h217, h223, hc03, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h0, h212, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h229 | h229
    · rcases m.htr 0 1 4 (by decide) (by decide) with h230 | h230
      · rcases m.htr 0 1 5 (by decide) (by decide) with h231 | h231
        · rcases m.htr 0 2 3 (by decide) (by decide) with h232 | h232
          · rcases m.htr 0 2 4 (by decide) (by decide) with h233 | h233
            · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
              · rcases m.htr 0 4 5 (by decide) (by decide) with h235 | h235
                · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                        · linarith only [h0, h229, h239, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h229, h234, h236, h239, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h238, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h229, h236, h237, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h229, h236, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h235, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h246 | h246
                · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                        · linarith only [h229, h234, h250, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                          · linarith only [h0, h230, h252, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h250, h252, hc13, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h229, h247, h249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h229, h247, h248, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h247, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h246, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h0, h230, h233, hlam]
          · linarith only [h0, h229, h232, hlam]
        · linarith only [h229, h231, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · rcases m.htr 0 3 4 (by decide) (by decide) with h265 | h265
              · linarith only [h229, h230, h265, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
                · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                        · linarith only [h229, h230, h265, h269, h271, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                            · linarith only [h230, h268, h271, h274, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                              · linarith only [h229, h230, h268, h269, h276, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h276, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h229, h230, h268, h273, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h229, h230, h268, h269, h270, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h264, h269, hc12, hlam, hphi, u2elo0]
                  · linarith only [h0, h229, h268, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h229, h230, h267, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
              · linarith only [h0, h229, h264, h284, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                    · linarith only [h0, h264, h288, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h229, h287, h288, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h287, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h229, h264, h286, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h229, h263, hlam]
        · linarith only [h229, h262, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h295 | h295
      · rcases m.htr 0 1 5 (by decide) (by decide) with h296 | h296
        · rcases m.htr 0 2 3 (by decide) (by decide) with h297 | h297
          · rcases m.htr 0 2 4 (by decide) (by decide) with h298 | h298
            · rcases m.htr 0 3 4 (by decide) (by decide) with h299 | h299
              · rcases m.htr 0 4 5 (by decide) (by decide) with h300 | h300
                · rcases m.htr 1 2 3 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h302 | h302
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h229, h295, h301, h305, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h305, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h229, h295, h297, h299, h302, h304, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h297, h303, hc23, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h229, h301, h302, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h295, h301, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h300, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h229, h295, h299, hlam]
            · linarith only [h229, h295, h297, h298, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 0 3 4 (by decide) (by decide) with h316 | h316
              · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                  · linarith only [h297, h315, h318, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h295, h318, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h317, hc04, hlam, hphi, ht45, u5elo4]
              · linarith only [h0, h295, h297, h316, hlam]
            · linarith only [h0, h295, h315, hlam]
        · linarith only [h295, h296, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h325 | h325
        · rcases m.htr 0 2 3 (by decide) (by decide) with h326 | h326
          · rcases m.htr 0 2 4 (by decide) (by decide) with h327 | h327
            · rcases m.htr 0 3 4 (by decide) (by decide) with h328 | h328
              · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
                · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h334 | h334
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                                  · linarith only [h326, h335, h338, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h338, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h295, h325, h333, h334, h337, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · linarith only [h336, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                              · linarith only [h229, h328, h330, h335, h343, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h343, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h295, h334, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h229, h328, h333, hlam]
                      · linarith only [h229, h328, h330, h332, hc34, hlam, hphi, ht45, u5elo2]
                    · linarith only [h229, h325, h330, h331, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h325, h330, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h329, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
                · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h355 | h355
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                        · linarith only [h229, h325, h328, h353, h355, h356, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                            · linarith only [h229, h325, h326, h355, h356, h359, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h361 | h361
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                                  · rcases h4bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h295, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h295, h354, h359, h361, h363, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p364_1, u2elo1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h328, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 4) (by simp) with h369 | h369
                                      · rcases p364_3 (m.d 1 4) (by simp) with h370 | h370
                                        · rcases p364_3 (m.d 2 4) (by simp) with h371 | h371
                                          · linarith only [h327, h371, hlam]
                                          · linarith only [h362, h371, hlam]
                                        · linarith only [h358, h370, hlam]
                                      · linarith only [h369, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h295, h325, h354, h355, h361, h363, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p364_1, u2elo1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h354, h359, h361, h363, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p364_1, u2elo1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h356, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 4) (by simp) with h380 | h380
                                      · linarith only [h295, h380, hlam]
                                      · linarith only [h352, h380, hlam]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h327, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h354, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h359, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h0, h327, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p364_1, u2elo1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 4) (by simp) with h388 | h388
                                      · linarith only [h328, h388, hlam]
                                      · rcases p364_3 (m.d 1 4) (by simp) with h390 | h390
                                        · linarith only [h356, h390, hlam]
                                        · linarith only [h295, h390, hlam]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h295, h325, h355, h361, h363, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 4) (by simp) with h394 | h394
                                      · linarith only [h328, h394, hlam]
                                      · linarith only [h327, h394, hlam]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h229, h325, h355, h356, h361, h363, hlam, p364_2]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h352, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h358, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h362, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h363, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                  · linarith only [h229, h325, h355, h356, h361, h363, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h229, h325, h358, h362, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                              · linarith only [h361, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h229, h325, h355, h356, h358, hc25, hlam, hphi, u5elo4]
                      · linarith only [h0, h355, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h229, h325, h327, h353, h354, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h325, h353, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h229, h325, h328, h352, hc15, hlam, hphi, u5elo4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h412 | h412
              · linarith only [h326, h327, h412, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h414 | h414
                · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                    · linarith only [h326, h327, h416, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h325, h416, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h325, h326, h415, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h414, hc04, hlam, hphi, ht45, u5elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h421 | h421
            · rcases m.htr 0 3 4 (by decide) (by decide) with h422 | h422
              · rcases m.htr 0 4 5 (by decide) (by decide) with h423 | h423
                · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
                  · linarith only [h326, h424, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h325, h424, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h295, h325, h423, hc15, hlam, hphi, u5elo4]
              · linarith only [h326, h421, h422, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
              · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
                · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
                  · linarith only [h326, h431, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h325, h431, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h430, hc04, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h435 | h435
                · rcases m.htr 1 2 3 (by decide) (by decide) with h436 | h436
                  · linarith only [h0, h325, h326, h436, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h0, h325, h436, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h429, h435, hc03, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h325, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_11_12_14_25_L_0_L_0_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
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
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · linarith only [h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h3, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
                  · linarith only [h12, h13, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h12, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h19, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · linarith only [h18, h19, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h17, h18, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h17, h24, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
                  · linarith only [h23, h24, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h23, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · linarith only [h30, h31, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h29, h3, h30, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h29, h36, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
                  · linarith only [h35, h36, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h3, h35, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h0, h42, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · linarith only [h41, h42, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h3, h40, h41, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                · linarith only [h1, h28, h4, h40, h46, hc24, hlam, hphi, ht45, u5elo4]
                · linarith only [h3, h46, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
          · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
              · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                · linarith only [h0, h3, h52, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
                  · linarith only [h0, h3, h54, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                  · linarith only [h51, h54, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                · linarith only [h3, h51, h57, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                  · linarith only [h0, h3, h59, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h1, h62, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · linarith only [h61, h62, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h1, h49, h61, h65, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h2, h67, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                        · linarith only [h3, h50, h57, h67, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
              · linarith only [h0, h3, h50, h70, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                · linarith only [h0, h3, h72, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h70, h74, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                      · linarith only [h1, h77, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · linarith only [h76, h77, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h49, h50, h76, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h81 | h81
            · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
              · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                · linarith only [h0, h3, h83, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                  · linarith only [h0, h3, h85, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
                  · linarith only [h82, h85, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                · linarith only [h3, h82, h88, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h90, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h1, h49, h92, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                      · linarith only [h1, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h2, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                        · linarith only [h3, h81, h88, h96, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
              · linarith only [h0, h3, h81, h99, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h101, h3, h81, hc24, hlam, hphi, ht45, u5elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h1, h103, h49, h81, h99, hlam, hphi, u5ehi7, u5elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                    · linarith only [h1, h105, h49, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                      · linarith only [h1, h107, h49, h81, hlam, hphi, u5ehi8, u5elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h1, h109, h2, h49, h81, h99, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                          · linarith only [h1, h111, h49, h99, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                            · linarith only [h107, h111, h113, h99, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h113, h99, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h116 | h116
        · linarith only [h0, h116, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h118 | h118
          · linarith only [h1, h118, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
              · linarith only [h0, h121, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                · linarith only [h1, h116, h121, h123, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h123, h2, hc12, hlam, hphi, u2elo3]
            · linarith only [h0, h120, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h127 | h127
      · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
        · rcases m.htr 0 3 4 (by decide) (by decide) with h129 | h129
          · rcases m.htr 0 4 5 (by decide) (by decide) with h130 | h130
            · linarith only [h1, h127, h130, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
              · linarith only [h0, h1, h132, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h132, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h127, h129, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
          · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
            · linarith only [h1, h127, h137, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
              · linarith only [h0, h1, h139, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h139, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h127, h136, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h143 | h143
        · linarith only [h0, h127, h143, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h145 | h145
          · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
            · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
              · linarith only [h0, h1, h147, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h147, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h127, h146, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h151 | h151
            · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
              · linarith only [h0, h1, h152, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h152, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h145, h151, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h156 | h156
    · rcases m.htr 0 1 4 (by decide) (by decide) with h157 | h157
      · rcases m.htr 0 2 4 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 3 4 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
            · linarith only [h0, h157, h160, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
              · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
                · rcases m.htr 1 2 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                    · linarith only [h0, h156, h165, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h156, h159, h165, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h164, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h156, h162, h163, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h162, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h171 | h171
            · linarith only [h0, h157, h171, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
              · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h0, h156, h159, h176, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h178 | h178
                      · linarith only [h0, h156, h178, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                        · linarith only [h0, h157, h171, h180, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                          · linarith only [h156, h159, h173, h182, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                            · linarith only [h173, h178, h184, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                              · linarith only [h157, h171, h174, h186, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                                · rcases h4bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h171, h176, h188, hc13, hc34, hlam, hphi, p189_1]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h171, h188, hc24, hlam, hphi, ht45, p189_1, u5elo3]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h159, hlam, p189_1]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h171, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h157, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h0, h157, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p189_1, u2elo1]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h176, hlam, p189_1]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h180, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h158, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h174, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h182, hlam, p189_1]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h186, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    rcases p189_3 (m.d 0 4) (by simp) with h205 | h205
                                    · linarith only [h159, h205, hlam]
                                    · rcases p189_3 (m.d 1 4) (by simp) with h207 | h207
                                      · linarith only [h176, h207, hlam]
                                      · rcases p189_3 (m.d 2 4) (by simp) with h209 | h209
                                        · linarith only [h182, h209, hlam]
                                        · rcases p189_3 (m.d 3 4) (by simp) with h211 | h211
                                          · rcases p189_3 (m.d 4 5) (by simp) with h212 | h212
                                            · linarith only [h188, h212, hlam]
                                            · linarith only [h171, h212, hlam]
                                          · linarith only [h159, h211, hlam]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    rcases p189_3 (m.d 0 4) (by simp) with h216 | h216
                                    · linarith only [h159, h216, hlam]
                                    · linarith only [h157, h216, hlam]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    rcases p189_3 (m.d 0 4) (by simp) with h219 | h219
                                    · linarith only [h159, h219, hlam]
                                    · linarith only [h158, h219, hlam]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h158, h171, h182, hc23, hc34, hlam, hphi, p189_1]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h157, hc14, hlam, hphi, ht45, p189_1, u5elo4]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h174, h182, hc23, hlam, hphi, ht34, ht45, p189_1, u5elo4]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h182, hc23, hlam, hphi, ht34, ht45, p189_1, u5elo4]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [h188, hlam, p189_0]
                                  · have p189_0 := h189c.1
                                    have p189_1 := h189c.2.1
                                    have p189_2 := h189c.2.2.1
                                    have p189_3 := h189c.2.2.2
                                    linarith only [hlam, p189_0]
                                · linarith only [h159, h188, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h175, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h156, h173, h174, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h173, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h0, h157, h158, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h234 | h234
        · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
          · linarith only [h156, h157, h235, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
            · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
              · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                    · linarith only [h156, h157, h235, h239, h241, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                      · linarith only [h156, h157, h239, h243, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                          · linarith only [h157, h241, h246, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                            · linarith only [h156, h157, h238, h243, h248, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                              · linarith only [h234, h250, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                                · rcases h4bigk with h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h157, hlam, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    rcases p253_3 (m.d 0 4) (by simp) with h256 | h256
                                    · rcases p253_3 (m.d 1 4) (by simp) with h257 | h257
                                      · rcases p253_3 (m.d 2 4) (by simp) with h258 | h258
                                        · linarith only [h234, h258, hlam]
                                        · rcases p253_3 (m.d 3 4) (by simp) with h260 | h260
                                          · rcases p253_3 (m.d 4 5) (by simp) with h261 | h261
                                            · linarith only [h237, h261, hlam]
                                            · linarith only [h250, h261, hlam]
                                          · linarith only [h246, h260, hlam]
                                      · linarith only [h239, h257, hlam]
                                    · linarith only [h234, h256, hlam]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h235, hlam, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h157, h239, h246, h250, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p253_1, u2elo1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h157, h239, hc01, hlam, hphi, ht12, p253_1, u2elo1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    rcases p253_3 (m.d 0 4) (by simp) with h271 | h271
                                    · linarith only [h157, h271, hlam]
                                    · linarith only [h234, h271, hlam]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h241, hlam, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h239, h246, h250, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p253_1, u2elo1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h234, hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h239, hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h246, hlam, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h250, hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h237, h246, h250, hc23, hc34, hlam, hphi, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h156, h157, h238, hc23, hc34, hlam, hphi, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    rcases p253_3 (m.d 0 4) (by simp) with h283 | h283
                                    · linarith only [h235, h283, hlam]
                                    · linarith only [h234, h283, hlam]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h246, h250, hc23, hc34, hlam, hphi, p253_1]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h237, hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h245, hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h157, h237, h246, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p253_1, u1elo3]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [h252, hlam, p253_0]
                                  · have p253_0 := h253c.1
                                    have p253_1 := h253c.2.1
                                    have p253_2 := h253c.2.2.1
                                    have p253_3 := h253c.2.2.2
                                    linarith only [hlam, p253_0]
                                · linarith only [h0, h234, h235, h237, h252, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h156, h157, h234, h237, h238, h245, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h234, h237, h240, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi9]
                · linarith only [h0, h156, h238, h239, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h238, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h156, h157, h237, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h299 | h299
          · linarith only [h0, h156, h234, h299, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
            · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
              · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
                · linarith only [h0, h156, h234, h302, h303, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h156, h302, h303, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h302, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h156, h157, h301, hc13, hlam, hphi, ht34, ht45, u5elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h308 | h308
      · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
        · rcases m.htr 0 3 4 (by decide) (by decide) with h310 | h310
          · rcases m.htr 0 4 5 (by decide) (by decide) with h311 | h311
            · linarith only [h0, h308, h311, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
              · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
                · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h317 | h317
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                        · linarith only [h156, h308, h311, h313, h318, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                            · linarith only [h313, h321, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                            · linarith only [h313, h317, h320, h321, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h310, h311, h320, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h156, h317, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h156, h308, h310, h314, h316, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h156, h308, h313, h314, h315, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h156, h313, h314, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h308, h313, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h156, h308, h310, hlam]
        · linarith only [h0, h308, h309, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h332 | h332
        · rcases m.htr 0 3 4 (by decide) (by decide) with h333 | h333
          · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
            · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
              · rcases m.htr 1 2 4 (by decide) (by decide) with h336 | h336
                · rcases m.htr 1 2 5 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
                            · linarith only [h335, h342, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                            · linarith only [h341, h342, hc34, hlam, hphi, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h345 | h345
                            · linarith only [h333, h341, h345, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h347 | h347
                              · linarith only [h332, h347, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h349 | h349
                                · linarith only [h156, h333, h335, h341, h347, h349, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                · linarith only [h308, h334, h341, h349, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h156, h308, h333, h334, h335, h340, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h156, h333, h334, h339, hlam, hphi, u5ehi9, u5elo3]
                    · linarith only [h156, h333, h338, hlam]
                  · linarith only [h156, h333, h334, h335, h337, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi9]
                · linarith only [h156, h333, h334, h335, h336, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi9]
              · linarith only [h0, h335, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
              · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
                · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                        · linarith only [h308, h334, h363, hc01, hlam, hphi, u1elo3]
                        · linarith only [h308, h363, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h156, h362, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h156, h333, h361, hlam]
                  · linarith only [h358, h360, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h156, h358, h359, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h358, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h371 | h371
            · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
              · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h375 | h375
                    · linarith only [h156, h333, h375, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                          · linarith only [h372, h375, h379, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                            · linarith only [h332, h379, h381, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                            · linarith only [h375, h377, h381, hc23, hc34, hlam, hphi]
                        · linarith only [h308, h378, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h156, h377, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h332, h371, h374, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi9]
                · linarith only [h0, h332, h373, hlam]
              · linarith only [h0, h332, h371, h372, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
              · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                    · linarith only [h156, h333, h392, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                        · linarith only [h308, h371, h390, h395, hc01, hlam, hphi, u1elo1]
                        · linarith only [h308, h395, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h156, h394, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h389, h391, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h156, h389, h390, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h389, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h402 | h402
          · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                · linarith only [h332, h405, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h405, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h404, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
              · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                · linarith only [h0, h332, h410, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h410, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h409, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h414 | h414
            · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
              · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                · linarith only [h0, h332, h416, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h416, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h415, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
              · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                · linarith only [h0, h332, h421, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h421, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h420, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
