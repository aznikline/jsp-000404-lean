import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · linarith only [h0, h5, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · linarith only [h0, h12, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h16, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · linarith only [h0, h16, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h19, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · linarith only [h0, h19, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h24 | h24
            · linarith only [h24, h4, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h26 | h26
              · linarith only [h26, h4, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                    · linarith only [h0, h24, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                            · rcases h0bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo0, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h28, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1, u0elo0, u3ehi4]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, h26, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo0, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo0, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h4, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h24, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h26, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h1, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo2, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, h1, h26, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo0, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, h1, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo0, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h2, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo3, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h28, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo3, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h3, hlam, p36_0]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p36_1, u0elo4, u2ehi1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h28, h29, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [h29, hlam, p36_1]
                              · have p36_0 := h36c.1
                                have p36_1 := h36c.2.1
                                have p36_2 := h36c.2.2.1
                                have p36_3 := h36c.2.2.2
                                linarith only [hlam, p36_0]
                            · linarith only [h1, h28, h29, h35, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h2, h24, h32, h34, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h33, h4, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h29, h30, h32, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                    · linarith only [h0, h24, h66, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h2, h29, h68, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h0, h24, h29, h71, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h0, h24, h71, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h28, h4, h70, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h4, h76, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                        · linarith only [h28, h4, h79, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h0, h4, h79, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h75, h76, h78, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h24, h83, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h2, h75, h85, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                        · linarith only [h0, h28, h4, h87, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h4, h87, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h90 | h90
          · rcases m.htr 0 2 4 (by decide) (by decide) with h91 | h91
            · rcases m.htr 0 2 5 (by decide) (by decide) with h92 | h92
              · linarith only [h0, h3, h92, hlam]
              · linarith only [h91, h92, hc25, hlam, hphi, u2ehi3]
            · linarith only [h90, h91, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
            · linarith only [h90, h96, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h98 | h98
              · linarith only [h90, h98, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
                · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                  · linarith only [h1, h100, h101, h3, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, h96, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                      · linarith only [h101, h105, h2, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h0, h105, h3, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                  · linarith only [h108, h2, h3, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                    · linarith only [h0, h110, h96, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                      · linarith only [h100, h108, h112, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h110, h112, h2, h3, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h115 | h115
        · rcases m.htr 0 2 3 (by decide) (by decide) with h116 | h116
          · rcases m.htr 0 2 4 (by decide) (by decide) with h117 | h117
            · linarith only [h0, h117, h2, hlam]
            · linarith only [h116, h117, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
            · linarith only [h116, h120, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
              · linarith only [h116, h122, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
                · linarith only [h1, h124, h2, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
                    · linarith only [h0, h120, h127, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · linarith only [h0, h127, h2, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h126, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h131 | h131
          · rcases m.htr 0 2 4 (by decide) (by decide) with h132 | h132
            · linarith only [h0, h132, h2, hlam]
            · linarith only [h131, h132, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h135 | h135
            · linarith only [h131, h135, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h137 | h137
              · linarith only [h131, h137, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
                · linarith only [h1, h139, h2, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                    · linarith only [h0, h135, h142, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · linarith only [h0, h142, h2, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h141, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h146 | h146
      · rcases m.htr 0 1 5 (by decide) (by decide) with h147 | h147
        · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
          · linarith only [h0, h1, h148, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h150 | h150
            · linarith only [h148, h150, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h152 | h152
              · linarith only [h148, h152, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
                · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                    · linarith only [h0, h1, h150, h156, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                            · rcases h0bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, h1, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo2, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h1, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h1, h146, h158, hc45, hlam, hphi, ht0b, ht5b, p162_1, u0elo2]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, h1, h152, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo2, u2ehi1]
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
                                linarith only [h148, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h150, hlam, p162_1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h152, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo2, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo2, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, h150, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo2, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, h152, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo2, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h146, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo3, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h154, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, h1, h146, h152, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p162_1, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h147, hlam, p162_0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p162_1, u0elo4, u2ehi1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h1, h146, h155, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u3ehi0]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [h155, hlam, p162_1]
                              · have p162_0 := h162c.1
                                have p162_1 := h162c.2.1
                                have p162_2 := h162c.2.2.1
                                have p162_3 := h162c.2.2.2
                                linarith only [hlam, p162_0]
                            · linarith only [h1, h147, h158, h161, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1, h146, h150, h158, h160, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h148, h159, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h1, h146, h155, h156, h158, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                    · linarith only [h0, h150, h192, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                      · linarith only [h1, h146, h155, h194, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
                          · linarith only [h0, h150, h155, h197, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h0, h150, h197, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h148, h154, h196, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                · linarith only [h0, h1, h154, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h202 | h202
          · linarith only [h0, h1, h202, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h204 | h204
            · linarith only [h202, h204, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
              · linarith only [h202, h206, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 0 4 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h146, h147, h209, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                    · linarith only [h0, h204, h211, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
                      · linarith only [h1, h146, h209, h213, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h147, h213, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h208, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h217 | h217
        · rcases m.htr 0 2 3 (by decide) (by decide) with h218 | h218
          · linarith only [h0, h1, h218, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h220 | h220
            · linarith only [h218, h220, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h222 | h222
              · linarith only [h218, h222, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
                · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                    · linarith only [h0, h220, h226, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                    · linarith only [h0, h146, h226, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h146, h225, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h224, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h231 | h231
          · linarith only [h0, h1, h231, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h233 | h233
            · linarith only [h231, h233, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
              · linarith only [h231, h235, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h237 | h237
                · rcases m.htr 0 4 5 (by decide) (by decide) with h238 | h238
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
                    · linarith only [h0, h217, h233, h237, h238, h239, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h0, h146, h239, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h146, h238, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h237, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h244 | h244
    · rcases m.htr 0 1 4 (by decide) (by decide) with h245 | h245
      · rcases m.htr 0 1 5 (by decide) (by decide) with h246 | h246
        · rcases m.htr 0 2 3 (by decide) (by decide) with h247 | h247
          · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
            · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 3 4 (by decide) (by decide) with h250 | h250
                · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h253 | h253
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                        · linarith only [h247, h254, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h0, h244, h250, h254, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h244, h250, h251, h252, h253, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h244, h252, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h260 | h260
                      · linarith only [h245, h251, h260, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                        · linarith only [h247, h262, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h250, h262, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · linarith only [h0, h244, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h266 | h266
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                        · linarith only [h244, h247, h250, h269, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h272 | h272
                            · rcases h0bigk with h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c | h273c
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h0, hlam, p273_1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h247, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p273_1, u0elo0, u2ehi2]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h0, h245, h267, h269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p273_1, u2ehi2]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h0, h249, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p273_1, u2ehi4]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h244, hlam, hphi, ht0b, ht34, ht45, ht5b, p273_1, u0elo1, u3ehi1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h247, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p273_1, u0elo1, u2ehi2]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h245, h267, h269, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p273_1, u0elo1, u2ehi2]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h249, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p273_1, u0elo1, u2ehi4]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h244, hlam, p273_1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h247, hlam, p273_1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h250, hlam, p273_1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h249, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p273_1, u0elo2, u2ehi4]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h245, hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h248, hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p273_1, u0elo3, u3ehi0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h0, h245, h249, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p273_1, u2ehi4]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h246, hlam, p273_0]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h249, hlam, p273_1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h247, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p273_1, u0elo4, u2ehi2]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [h266, hlam, p273_1]
                              · have p273_0 := h273c.1
                                have p273_1 := h273c.2.1
                                have p273_2 := h273c.2.2.1
                                have p273_3 := h273c.2.2.2
                                linarith only [hlam, p273_0]
                            · linarith only [h0, h245, h267, h271, h272, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h245, h266, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h245, h266, h267, h268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h244, h267, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h304 | h304
                      · linarith only [h0, h245, h266, h304, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                        · linarith only [h247, h250, h306, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                          · linarith only [h245, h266, h303, h308, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h245, h266, h303, h306, h310, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h247, h250, h310, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h249, h303, hc24, hlam, hphi, u2ehi4]
              · linarith only [h247, h249, hc25, hlam, hphi, u2ehi2]
            · linarith only [h247, h248, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h244, h247, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h317 | h317
          · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
            · rcases m.htr 0 2 5 (by decide) (by decide) with h319 | h319
              · rcases m.htr 0 3 4 (by decide) (by decide) with h320 | h320
                · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                  · linarith only [h244, h246, h320, h321, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h245, h321, h324, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h245, h246, h323, h324, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                    · linarith only [h0, h319, h323, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                  · linarith only [h245, h246, h328, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                      · linarith only [h245, h320, h328, h331, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · linarith only [h244, h246, h331, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h244, h330, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h318, h319, hc25, hlam, hphi, u2ehi3]
            · linarith only [h317, h318, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h244, h317, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h338 | h338
        · rcases m.htr 0 2 3 (by decide) (by decide) with h339 | h339
          · rcases m.htr 0 2 4 (by decide) (by decide) with h340 | h340
            · rcases m.htr 0 2 5 (by decide) (by decide) with h341 | h341
              · rcases m.htr 0 3 4 (by decide) (by decide) with h342 | h342
                · linarith only [h244, h245, h342, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                        · linarith only [h339, h342, h347, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h349 | h349
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h350 | h350
                            · rcases h0bigk with h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [hlam, p351_0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h0, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h339, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1, u0elo0, u2ehi2]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h245, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h245, h341, h345, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p351_1, u2ehi4]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h244, hlam, hphi, ht0b, ht34, ht45, ht5b, p351_1, u0elo1, u3ehi1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [hlam, p351_0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h339, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1, u0elo1, u2ehi2]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h244, h245, hlam, hphi, ht0b, ht34, ht45, ht5b, p351_1, u0elo1, u3ehi1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h341, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1, u0elo1, u2ehi4]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h244, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h339, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [hlam, p351_0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h342, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h341, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1, u0elo2, u2ehi4]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h244, hlam, hphi, ht0b, ht34, ht45, ht5b, p351_1, u0elo3, u3ehi1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h340, hlam, p351_0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h340, hlam, hphi, ht0b, ht34, ht45, ht5b, p351_1, u0elo1, u3ehi0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [hlam, p351_0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h340, h341, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1, u0elo1, u2ehi4]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h338, hlam, p351_0]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h341, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h339, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p351_1, u0elo4, u2ehi2]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [h344, hlam, p351_1]
                              · have p351_0 := h351c.1
                                have p351_1 := h351c.2.1
                                have p351_2 := h351c.2.2.1
                                have p351_3 := h351c.2.2.2
                                linarith only [hlam, p351_0]
                            · linarith only [h340, h349, h350, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h340, h344, h349, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h244, h245, h340, h344, h346, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                    · linarith only [h0, h244, h345, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h244, h245, h344, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h340, h341, hc25, hlam, hphi, u2ehi3]
            · linarith only [h339, h340, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h244, h339, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h385 | h385
          · rcases m.htr 0 2 4 (by decide) (by decide) with h386 | h386
            · rcases m.htr 0 2 5 (by decide) (by decide) with h387 | h387
              · rcases m.htr 0 3 4 (by decide) (by decide) with h388 | h388
                · linarith only [h244, h245, h388, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                        · linarith only [h385, h388, h393, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h396 | h396
                            · rcases h0bigk with h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [hlam, p397_0]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h0, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h385, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p397_1, u0elo0, u2ehi2]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h245, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h338, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo1, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [hlam, p397_0]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h385, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p397_1, u0elo1, u2ehi2]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, h245, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo1, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, h338, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo1, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h385, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [hlam, p397_0]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h388, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, h338, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo2, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo3, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h386, hlam, p397_0]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h386, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo1, u3ehi0]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [hlam, p397_0]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, h338, h386, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo1, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h244, hlam, hphi, ht0b, ht34, ht45, ht5b, p397_1, u0elo4, u3ehi1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h387, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h385, h386, h390, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p397_1, u0elo1, u2ehi2]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [h390, hlam, p397_1]
                              · have p397_0 := h397c.1
                                have p397_1 := h397c.2.1
                                have p397_2 := h397c.2.2.1
                                have p397_3 := h397c.2.2.2
                                linarith only [hlam, p397_0]
                            · linarith only [h386, h388, h395, h396, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h390, h395, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                      · linarith only [h244, h245, h386, h390, h392, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                    · linarith only [h0, h244, h391, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h244, h245, h390, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h386, h387, hc25, hlam, hphi, u2ehi3]
            · linarith only [h385, h386, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h244, h385, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h431 | h431
      · rcases m.htr 0 1 5 (by decide) (by decide) with h432 | h432
        · rcases m.htr 0 2 3 (by decide) (by decide) with h433 | h433
          · rcases m.htr 0 2 4 (by decide) (by decide) with h434 | h434
            · rcases m.htr 0 2 5 (by decide) (by decide) with h435 | h435
              · rcases m.htr 0 3 4 (by decide) (by decide) with h436 | h436
                · rcases m.htr 0 4 5 (by decide) (by decide) with h437 | h437
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h439 | h439
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h440 | h440
                        · linarith only [h433, h440, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h436, h440, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h431, h437, h438, h439, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · linarith only [h0, h435, h438, hc24, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                      · linarith only [h431, h437, h446, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                        · linarith only [h433, h448, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h433, h436, h448, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h435, h445, hc24, hlam, hphi, u2ehi4]
                · linarith only [h244, h431, h436, hlam]
              · linarith only [h433, h435, hc25, hlam, hphi, u2ehi2]
            · linarith only [h433, h434, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h455 | h455
            · linarith only [h433, h455, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h431, h455, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h458 | h458
          · rcases m.htr 0 2 4 (by decide) (by decide) with h459 | h459
            · rcases m.htr 0 2 5 (by decide) (by decide) with h460 | h460
              · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
                · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
                  · linarith only [h431, h432, h462, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                      · linarith only [h431, h462, h465, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h431, h432, h464, h465, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                    · linarith only [h0, h460, h464, hc24, hlam, hphi, u2ehi4]
                · linarith only [h244, h431, h461, hlam]
              · linarith only [h458, h460, hc25, hlam, hphi, u2ehi2]
            · linarith only [h458, h459, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h472 | h472
            · linarith only [h458, h472, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h431, h472, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h475 | h475
        · rcases m.htr 0 2 3 (by decide) (by decide) with h476 | h476
          · rcases m.htr 0 2 4 (by decide) (by decide) with h477 | h477
            · rcases m.htr 0 2 5 (by decide) (by decide) with h478 | h478
              · rcases m.htr 0 3 4 (by decide) (by decide) with h479 | h479
                · rcases m.htr 0 4 5 (by decide) (by decide) with h480 | h480
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                        · linarith only [h476, h483, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h479, h483, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · linarith only [h431, h475, h478, h482, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h477, h481, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                  · linarith only [h431, h475, h480, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                        · linarith only [h476, h492, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h495 | h495
                            · rcases h0bigk with h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c | h496c
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h0, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h244, hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h431, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h244, h478, h479, hc34, hlam, hphi, ht23, p496_1, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h475, hc15, hlam, hphi, ht0b, ht5b, p496_1, u0elo1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p496_1, u0elo1, u3ehi0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h244, h475, h478, h479, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p496_1, u0elo1, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h478, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p496_1, u0elo1, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h475, h478, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p496_1, u0elo2, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h476, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h479, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h478, h479, hc34, hlam, hphi, ht23, p496_1, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h475, h477, h478, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p496_1, u0elo1, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h477, hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h477, hlam, hphi, ht0b, ht34, ht45, ht5b, p496_1, u0elo1, u3ehi0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h477, h478, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p496_1, u0elo1, u2ehi4]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h475, hlam, p496_0]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h478, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h244, h475, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [h489, hlam, p496_1]
                              · have p496_0 := h496c.1
                                have p496_1 := h496c.2.1
                                have p496_2 := h496c.2.2.1
                                have p496_3 := h496c.2.2.2
                                linarith only [hlam, p496_0]
                            · linarith only [h475, h491, h495, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h244, h475, h479, h491, h492, h494, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h431, h475, h478, h491, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h0, h477, h490, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h244, h475, h479, h489, hlam]
              · linarith only [h476, h478, hc25, hlam, hphi, u2ehi2]
            · linarith only [h476, h477, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h529 | h529
            · linarith only [h476, h529, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h531 | h531
              · linarith only [h476, h531, hc23, hlam, hphi, u2ehi4]
              · linarith only [h0, h475, h531, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h534 | h534
          · rcases m.htr 0 2 4 (by decide) (by decide) with h535 | h535
            · rcases m.htr 0 2 5 (by decide) (by decide) with h536 | h536
              · rcases m.htr 0 3 4 (by decide) (by decide) with h537 | h537
                · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h540 | h540
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h541 | h541
                        · linarith only [h534, h541, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h534, h537, h541, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h431, h534, h537, h538, h540, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h535, h539, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h547 | h547
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h548 | h548
                        · linarith only [h534, h548, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h534, h537, h548, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h551 | h551
                        · linarith only [h534, h551, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h534, h537, h551, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h535, h536, h546, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                        · linarith only [h534, h537, h558, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h560 | h560
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h561 | h561
                            · rcases h0bigk with h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [hlam, p562_0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h0, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h244, hlam, p562_0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h431, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h475, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                rcases p562_3 (m.d 0 1) (by simp) with h568 | h568
                                · linarith only [h0, h568, hlam]
                                · rcases p562_3 (m.d 0 2) (by simp) with h570 | h570
                                  · rcases p562_3 (m.d 0 3) (by simp) with h571 | h571
                                    · linarith only [h534, h571, hlam]
                                    · linarith only [h244, h571, hlam]
                                  · linarith only [h0, h570, hlam]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [hlam, p562_0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h534, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p562_1, u0elo1, u2ehi2]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h535, h560, hc45, hlam, hphi, ht0b, ht5b, p562_1, u0elo1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h536, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p562_1, u0elo1, u2ehi4]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h537, hc01, hc34, hlam, hphi, ht12, ht23, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h534, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [hlam, p562_0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h537, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h536, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p562_1, u0elo2, u2ehi4]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                rcases p562_3 (m.d 0 1) (by simp) with h584 | h584
                                · linarith only [h431, h584, hlam]
                                · rcases p562_3 (m.d 0 2) (by simp) with h586 | h586
                                  · rcases p562_3 (m.d 0 3) (by simp) with h587 | h587
                                    · linarith only [h537, h587, hlam]
                                    · linarith only [h244, h587, hlam]
                                  · linarith only [h0, h586, hlam]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h535, hlam, p562_0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h535, hlam, hphi, ht0b, ht34, ht45, ht5b, p562_1, u0elo1, u3ehi0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [hlam, p562_0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h535, h536, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p562_1, u0elo1, u2ehi4]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                rcases p562_3 (m.d 0 1) (by simp) with h595 | h595
                                · linarith only [h475, h595, hlam]
                                · rcases p562_3 (m.d 0 2) (by simp) with h597 | h597
                                  · rcases p562_3 (m.d 0 3) (by simp) with h598 | h598
                                    · linarith only [h537, h598, hc01, hc34, hlam, hphi, ht12, ht23, p562_1]
                                    · linarith only [h244, h598, hlam]
                                  · linarith only [h0, h597, hlam]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h536, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p562_1, u0elo4, u3ehi0]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [h555, hlam, p562_1]
                              · have p562_0 := h562c.1
                                have p562_1 := h562c.2.1
                                have p562_2 := h562c.2.2.1
                                have p562_3 := h562c.2.2.2
                                linarith only [hlam, p562_0]
                            · linarith only [h534, h537, h561, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h535, h555, h560, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h431, h555, h557, hlam]
                    · linarith only [h0, h534, h556, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h610 | h610
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                        · linarith only [h534, h537, h612, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                          · linarith only [h534, h535, h537, h555, h614, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h616 | h616
                            · linarith only [h534, h537, h555, h616, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h534, h537, h610, h611, h616, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                        · linarith only [h534, h537, h619, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h621 | h621
                          · linarith only [h431, h535, h611, h621, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h623 | h623
                            · linarith only [h431, h611, h623, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h534, h537, h623, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h536, h610, hc24, hlam, hphi, u2ehi4]
              · linarith only [h534, h536, hc25, hlam, hphi, u2ehi2]
            · linarith only [h534, h535, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h629 | h629
            · linarith only [h534, h629, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h631 | h631
              · linarith only [h534, h631, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h633 | h633
                · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h639 | h639
                            · rcases h0bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h0, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h244, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h431, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h475, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, h635, h638, hc01, hc12, hlam, hphi, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h534, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h629, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h651 | h651
                                · linarith only [h244, h651, hlam]
                                · rcases p640_3 (m.d 0 2) (by simp) with h653 | h653
                                  · linarith only [h534, h653, hlam]
                                  · linarith only [h0, h653, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, u0elo2, u2ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, h634, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, u0elo2, u2ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, u0elo2, u2ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h629, h635, hc01, hc12, hlam, hphi, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h629, h635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h633, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h629, h631, h635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, h635, h638, hc01, hc12, hlam, hphi, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, h635, h638, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h631, h635, h638, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p640_1, u3ehi0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h634, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                            · linarith only [h629, h634, h635, h639, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h629, h634, h638, hlam]
                        · linarith only [h534, h637, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h629, h634, h635, h636, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h675 | h675
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h677 | h677
                            · rcases h0bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h0, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h244, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h431, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h475, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h0, h635, h675, hc01, hc23, hlam, hphi, ht12, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h534, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h629, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h631, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h689 | h689
                                · linarith only [h244, h689, hlam]
                                · rcases p678_3 (m.d 0 2) (by simp) with h691 | h691
                                  · linarith only [h534, h691, hlam]
                                  · linarith only [h0, h691, hlam]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u0elo2, u2ehi0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h629, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u0elo2, u2ehi0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h631, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u0elo2, u2ehi0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h698 | h698
                                · linarith only [h431, h698, hlam]
                                · rcases p678_3 (m.d 0 2) (by simp) with h700 | h700
                                  · linarith only [h629, h700, hlam]
                                  · linarith only [h0, h700, hlam]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h633, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u0elo2, u2ehi0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h633, hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h631, h633, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u0elo2, u2ehi0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                rcases p678_3 (m.d 0 1) (by simp) with h707 | h707
                                · linarith only [h475, h707, hlam]
                                · rcases p678_3 (m.d 0 2) (by simp) with h709 | h709
                                  · linarith only [h631, h709, hlam]
                                  · linarith only [h0, h709, hlam]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h633, h634, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u0elo2, u2ehi0]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h633, h634, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [h634, hlam, p678_1]
                              · have p678_0 := h678c.1
                                have p678_1 := h678c.2.1
                                have p678_2 := h678c.2.2.1
                                have p678_3 := h678c.2.2.2
                                linarith only [hlam, p678_0]
                            · linarith only [h633, h634, h677, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                          · linarith only [h633, h634, h635, h676, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                        · linarith only [h534, h675, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h431, h634, h674, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h720 | h720
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h721 | h721
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h722 | h722
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h723 | h723
                          · linarith only [h629, h634, h723, hc24, hlam, hphi, u2ehi0]
                          · linarith only [h629, h720, h721, h723, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h534, h633, h634, h720, h721, h722, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h629, h720, h721, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h728 | h728
                      · linarith only [h629, h634, h720, h728, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h730 | h730
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
                          · linarith only [h431, h728, h730, h731, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h629, h731, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h633, h730, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h735 | h735
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h736 | h736
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h737 | h737
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h738 | h738
                        · linarith only [h534, h633, h738, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h534, h738, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h735, h736, h737, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                        · linarith only [h534, h633, h743, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h534, h743, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h431, h735, h742, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h747 | h747
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h748 | h748
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h749 | h749
                        · linarith only [h534, h633, h749, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h534, h749, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h629, h747, h748, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h753 | h753
                      · linarith only [h534, h633, h735, h747, h753, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h755 | h755
                        · linarith only [h534, h633, h755, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h534, h755, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
