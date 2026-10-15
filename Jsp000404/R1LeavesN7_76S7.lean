import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h0, h4, h7, h8, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                  · linarith only [h0, h3, h6, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h2, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h1, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
              · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h0, h17, h18, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h15, h17, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h15, h16, hc24, hlam, hphi, u2ehi2]
              · linarith only [h1, h15, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h24 | h24
            · linarith only [h24, h3, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
                · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h0, h29, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h24, h28, h31, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h0, h26, h34, h4, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                            · linarith only [h2, h31, h36, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                              · linarith only [h0, h24, h26, h33, h38, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases h3bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h26, h33, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1, u0elo4]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h38, h4, hc45, hlam, hphi, ht23, ht34, p40_1, u2ehi2]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h38, h4, hc34, hc45, hlam, hphi, p40_1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h4, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h0, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u0elo0, u2ehi2]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1, u0elo0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h29, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h26, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1, u0elo1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h34, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h3, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h28, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h33, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h38, hlam, p40_1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, h38, hc45, hlam, hphi, ht23, ht34, p40_1, u2ehi2]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h27, h28, h38, hc45, hlam, hphi, ht23, ht34, p40_1, u2ehi3]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h33, h38, hc45, hlam, hphi, ht23, ht34, p40_1, u2ehi3]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 3) (by simp) with h64 | h64
                                  · linarith only [h4, h64, hlam]
                                  · linarith only [h3, h64, hlam]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                        · linarith only [h3, h33, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h28, h3, h4, hc13, hc35, hlam, hphi]
                · linarith only [h2, h26, h27, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi2]
              · linarith only [h1, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
          · rcases m.htr 0 4 5 (by decide) (by decide) with h73 | h73
            · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
              · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
                · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                  · linarith only [h0, h3, h76, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h0, h78, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h3, h72, h74, h78, hc23, hc34, hlam, hphi]
                · linarith only [h2, h75, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h1, h74, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h3, h72, h73, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h84 | h84
            · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
              · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                  · linarith only [h0, h3, h87, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h72, h89, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                        · linarith only [h0, h3, h85, h92, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                          · linarith only [h0, h72, h85, h94, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h2, h96, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · linarith only [h84, h96, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                      · linarith only [h2, h84, h86, h91, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                · linarith only [h85, h86, hc24, hlam, hphi, u2ehi2]
              · linarith only [h1, h85, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
              · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h0, h104, h3, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h0, h106, h72, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                      · linarith only [h104, h108, h2, h84, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                        · linarith only [h0, h102, h110, h3, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                          · linarith only [h0, h102, h112, h72, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                            · linarith only [h108, h114, h2, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                              · linarith only [h0, h102, h116, h3, h84, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h0, h102, h116, h3, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h103, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h1, h102, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h122 | h122
      · linarith only [h1, h122, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h124 | h124
        · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
          · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
            · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
              · linarith only [h0, h1, h127, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
                · linarith only [h122, h127, h129, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                    · linarith only [h0, h132, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h0, h125, h129, h131, h132, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                  · linarith only [h0, h124, h127, h131, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
              · linarith only [h0, h1, h125, h136, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                · linarith only [h122, h136, h138, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h141 | h141
                    · linarith only [h0, h141, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h125, h140, h141, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h124, h136, h140, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
            · linarith only [h124, h125, h145, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
              · linarith only [h0, h1, h147, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                · linarith only [h122, h147, h149, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h152 | h152
                    · linarith only [h0, h125, h152, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                      · linarith only [h0, h122, h145, h151, h154, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h1, h125, h157, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1, h157, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h1, h151, h156, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · linarith only [h124, h125, h151, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h162 | h162
          · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
            · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
              · linarith only [h0, h1, h164, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                · linarith only [h122, h164, h166, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                  · linarith only [h0, h124, h168, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                    · linarith only [h0, h170, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h124, h162, h170, hc13, hc34, hlam, hphi]
            · linarith only [h124, h162, h163, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h174 | h174
            · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
              · linarith only [h0, h1, h175, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                · linarith only [h122, h174, h175, h177, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                  · linarith only [h0, h124, h179, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                    · linarith only [h0, h162, h181, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                        · linarith only [h0, h124, h175, h184, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1, h184, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h174, h177, h183, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
              · linarith only [h0, h1, h162, h188, hc35, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
                · linarith only [h122, h188, h190, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h0, h124, h192, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h0, h194, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                      · linarith only [h122, h174, h190, h196, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                        · linarith only [h0, h124, h188, h198, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1, h198, hc34, hlam, hphi, ht23, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h201 | h201
    · rcases m.htr 0 2 4 (by decide) (by decide) with h202 | h202
      · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
        · rcases m.htr 0 3 5 (by decide) (by decide) with h204 | h204
          · rcases m.htr 0 4 5 (by decide) (by decide) with h205 | h205
            · rcases m.htr 1 2 3 (by decide) (by decide) with h206 | h206
              · rcases m.htr 1 2 4 (by decide) (by decide) with h207 | h207
                · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                          · linarith only [h201, h212, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h204, h211, h212, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h201, h203, h211, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · linarith only [h205, h207, h210, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h0, h204, h209, hlam]
                  · linarith only [h0, h203, h208, hlam]
                · linarith only [h0, h202, h203, h205, h206, h207, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
              · linarith only [h201, h206, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h201, h227, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h204, h226, h227, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h201, h203, h226, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                          · linarith only [h201, h232, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h201, h204, h232, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h201, h203, h231, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h204, h224, hlam]
                  · linarith only [h0, h203, h204, h223, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
                · linarith only [h202, h222, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h201, h221, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h240 | h240
            · linarith only [h203, h204, h240, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
              · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                          · linarith only [h202, h203, h204, h248, hc23, hlam, hphi, u2ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                            · linarith only [h202, h240, h250, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                              · linarith only [h202, h240, h252, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases h3bigk with h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c | h254c
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h0, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h204, h242, h244, h246, h252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h204, h242, h244, h246, h252, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h204, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  rcases p254_3 (m.d 0 3) (by simp) with h260 | h260
                                  · linarith only [h0, h260, hlam]
                                  · rcases p254_3 (m.d 1 3) (by simp) with h262 | h262
                                    · rcases p254_3 (m.d 2 3) (by simp) with h263 | h263
                                      · linarith only [h242, h263, hlam]
                                      · rcases p254_3 (m.d 3 4) (by simp) with h265 | h265
                                        · linarith only [h244, h265, hlam]
                                        · rcases p254_3 (m.d 3 5) (by simp) with h267 | h267
                                          · linarith only [h245, h267, hlam]
                                          · linarith only [h204, h267, hlam]
                                    · linarith only [h0, h262, hlam]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  rcases p254_3 (m.d 0 3) (by simp) with h272 | h272
                                  · linarith only [h0, h272, hlam]
                                  · linarith only [h201, h272, hlam]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h203, h204, h244, h246, h252, hlam, p254_2]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h203, h204, h242, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h201, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h242, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h201, hc34, hlam, hphi, ht0b, ht45, ht5b, p254_1, u0elo1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h248, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h203, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h244, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h247, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h252, hlam, p254_1]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h202, h203, hc35, hlam, hphi, ht23, p254_1, u2ehi3]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h245, hlam, p254_0]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [h242, h245, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p254_1, u2ehi2]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  rcases p254_3 (m.d 0 3) (by simp) with h290 | h290
                                  · linarith only [h204, h290, hlam]
                                  · linarith only [h203, h290, hlam]
                                · have p254_0 := h254c.1
                                  have p254_1 := h254c.2.1
                                  have p254_2 := h254c.2.2.1
                                  have p254_3 := h254c.2.2.2
                                  linarith only [hlam, p254_0]
                        · linarith only [h203, h204, h247, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                          · linarith only [h201, h204, h296, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                            · linarith only [h202, h246, h298, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h300 | h300
                              · linarith only [h201, h204, h245, h246, h295, h300, hlam]
                              · rcases h3bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h0, hlam, p302_1]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h204, h242, h245, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p302_1]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h204, h242, h245, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p302_1]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h204, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  rcases p302_3 (m.d 0 3) (by simp) with h308 | h308
                                  · linarith only [h0, h308, hlam]
                                  · rcases p302_3 (m.d 1 3) (by simp) with h310 | h310
                                    · rcases p302_3 (m.d 2 3) (by simp) with h311 | h311
                                      · linarith only [h242, h311, hlam]
                                      · rcases p302_3 (m.d 3 4) (by simp) with h313 | h313
                                        · linarith only [h244, h313, hlam]
                                        · rcases p302_3 (m.d 3 5) (by simp) with h315 | h315
                                          · linarith only [h245, h315, hlam]
                                          · linarith only [h204, h315, hlam]
                                    · linarith only [h0, h310, hlam]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  rcases p302_3 (m.d 0 3) (by simp) with h320 | h320
                                  · linarith only [h0, h320, hlam]
                                  · linarith only [h201, h320, hlam]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h203, h204, h245, hlam, p302_2]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h202, h203, h204, h242, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p302_1, u2ehi3]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h201, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h242, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h201, hc34, hlam, hphi, ht0b, ht45, ht5b, p302_1, u0elo1]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h296, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h203, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h244, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h295, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h300, hlam, p302_1]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h202, h203, hc35, hlam, hphi, ht23, p302_1, u2ehi3]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h245, hlam, p302_0]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [h242, h245, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p302_1, u2ehi2]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  rcases p302_3 (m.d 0 3) (by simp) with h338 | h338
                                  · linarith only [h204, h338, hlam]
                                  · linarith only [h203, h338, hlam]
                                · have p302_0 := h302c.1
                                  have p302_1 := h302c.2.1
                                  have p302_2 := h302c.2.2.1
                                  have p302_3 := h302c.2.2.2
                                  linarith only [hlam, p302_0]
                        · linarith only [h203, h204, h242, h245, h295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
                      · linarith only [h202, h240, h244, h245, h343, hc35, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                          · linarith only [h0, h245, h346, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h348 | h348
                            · linarith only [h202, h240, h348, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h350 | h350
                              · linarith only [h202, h240, h350, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases h3bigk with h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c | h352c
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h0, hlam, p352_1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h345, hc34, hlam, hphi, ht0b, ht45, ht5b, p352_1, u0elo2]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h0, h245, h350, hc34, hc45, hlam, hphi, p352_1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h204, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h245, h350, hc03, hc45, hlam, hphi, ht34, p352_1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h245, h350, hc45, hlam, hphi, ht23, ht34, p352_1, u2ehi2]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h245, h350, hc34, hc45, hlam, hphi, p352_1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h245, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h201, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h242, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h201, hc34, hlam, hphi, ht0b, ht45, ht5b, p352_1, u0elo1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h346, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h203, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h244, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h345, hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [hlam, p352_0]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h350, hlam, p352_1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h201, h350, hc45, hlam, hphi, ht23, ht34, p352_1, u2ehi2]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h0, h350, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p352_1]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [h345, h350, hc45, hlam, hphi, ht23, ht34, p352_1, u2ehi3]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  rcases p352_3 (m.d 0 3) (by simp) with h376 | h376
                                  · linarith only [h204, h376, hlam]
                                  · linarith only [h203, h376, hlam]
                                · have p352_0 := h352c.1
                                  have p352_1 := h352c.2.1
                                  have p352_2 := h352c.2.2.1
                                  have p352_3 := h352c.2.2.2
                                  linarith only [hlam, p352_0]
                        · linarith only [h203, h345, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h203, h244, hlam]
                · linarith only [h202, h243, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h201, h242, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
          · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
            · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
              · rcases m.htr 1 2 4 (by decide) (by decide) with h387 | h387
                · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                  · linarith only [h203, h384, h388, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h391 | h391
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h392 | h392
                        · linarith only [h201, h388, h392, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h394 | h394
                          · linarith only [h202, h392, h394, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                          · linarith only [h0, h384, h388, h394, hc23, hc34, hlam, hphi]
                      · linarith only [h385, h387, h391, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h0, h384, h390, hlam]
                · linarith only [h386, h387, hc24, hlam, hphi, u2ehi2]
              · linarith only [h201, h386, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h203, h384, h385, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
            · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
              · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
                · rcases m.htr 1 3 4 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                        · linarith only [h201, h203, h408, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
                          · linarith only [h201, h384, h410, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                            · linarith only [h202, h412, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · linarith only [h203, h402, h403, h405, h412, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h203, h402, h403, h404, h405, h407, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h203, h405, h406, hc03, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                    · linarith only [h201, h384, h405, h417, hc34, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
                        · linarith only [h201, h203, h420, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h422 | h422
                          · linarith only [h0, h201, h417, h422, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
                            · linarith only [h202, h424, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · linarith only [h402, h424, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                      · linarith only [h202, h402, h404, h419, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                · linarith only [h202, h404, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h201, h403, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
              · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                        · linarith only [h201, h203, h435, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
                          · linarith only [h201, h203, h402, h430, h432, h434, h437, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                            · linarith only [h202, h402, h439, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h441 | h441
                              · linarith only [h201, h203, h402, h441, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h201, h203, h430, h432, h434, h441, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h201, h203, h432, h434, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h201, h203, h432, h433, hc35, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                    · linarith only [h201, h384, h432, h446, hc34, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                      · linarith only [h202, h402, h432, h448, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                        · linarith only [h201, h203, h450, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                          · linarith only [h0, h201, h446, h452, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h454 | h454
                            · linarith only [h202, h402, h454, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h456 | h456
                              · linarith only [h0, h201, h432, h448, h456, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h201, h203, h456, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h202, h431, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h201, h203, h430, hc34, hlam, hphi, ht23, u2ehi1]
      · linarith only [h201, h202, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h462 | h462
      · linarith only [h201, h462, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h464 | h464
        · rcases m.htr 0 3 5 (by decide) (by decide) with h465 | h465
          · rcases m.htr 0 4 5 (by decide) (by decide) with h466 | h466
            · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
              · rcases m.htr 1 2 4 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h475 | h475
                              · linarith only [h464, h475, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                              · rcases h3bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h0, hlam, p477_1]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h201, hlam, p477_1]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  rcases p477_3 (m.d 0 3) (by simp) with h481 | h481
                                  · rcases p477_3 (m.d 1 3) (by simp) with h482 | h482
                                    · rcases p477_3 (m.d 2 3) (by simp) with h483 | h483
                                      · rcases p477_3 (m.d 3 4) (by simp) with h484 | h484
                                        · linarith only [h484, hlam, p477_0]
                                        · rcases p477_3 (m.d 3 5) (by simp) with h486 | h486
                                          · linarith only [h465, h486, hlam]
                                          · linarith only [h475, h486, hlam]
                                      · linarith only [h472, h483, hlam]
                                    · linarith only [h469, h482, hlam]
                                  · linarith only [h481, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h201, h467, hc12, hlam, hphi, ht01, ht0b, ht5b, p477_1, u5ehi3]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h464, h466, h475, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p477_1]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h462, h467, h472, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p477_1, u2ehi0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  rcases p477_3 (m.d 0 3) (by simp) with h496 | h496
                                  · linarith only [h0, h496, hlam]
                                  · linarith only [h464, h496, hlam]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  rcases p477_3 (m.d 0 3) (by simp) with h499 | h499
                                  · linarith only [h0, h499, hlam]
                                  · linarith only [h465, h499, hlam]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h464, h466, h475, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p477_1]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h467, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  rcases p477_3 (m.d 0 3) (by simp) with h505 | h505
                                  · linarith only [h201, h505, hlam]
                                  · linarith only [h464, h505, hlam]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h467, hc12, hlam, hphi, ht01, ht0b, ht5b, p477_1, u5ehi3]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h464, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h469, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h472, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h475, hlam, p477_1]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h465, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h470, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h473, hlam, p477_0]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [h465, hc34, hlam, hphi, ht0b, ht45, ht5b, p477_1, u0elo2]
                                · have p477_0 := h477c.1
                                  have p477_1 := h477c.2.1
                                  have p477_2 := h477c.2.2.1
                                  have p477_3 := h477c.2.2.2
                                  linarith only [hlam, p477_0]
                            · linarith only [h462, h466, h474, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                          · linarith only [h201, h465, h473, hlam]
                        · linarith only [h201, h472, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h462, h464, h466, h468, h471, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                    · linarith only [h0, h201, h465, h467, h470, hc01, hc12, hlam, hphi]
                  · linarith only [h201, h464, h467, h469, hlam]
                · linarith only [h201, h465, h467, h468, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
                · linarith only [h467, h526, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                              · linarith only [h464, h534, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                              · rcases h3bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h201, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 3) (by simp) with h540 | h540
                                  · rcases p536_3 (m.d 1 3) (by simp) with h541 | h541
                                    · rcases p536_3 (m.d 2 3) (by simp) with h542 | h542
                                      · rcases p536_3 (m.d 3 4) (by simp) with h543 | h543
                                        · linarith only [h543, hlam, p536_0]
                                        · rcases p536_3 (m.d 3 5) (by simp) with h545 | h545
                                          · linarith only [h465, h545, hlam]
                                          · linarith only [h534, h545, hlam]
                                      · linarith only [h531, h542, hlam]
                                    · linarith only [h528, h541, hlam]
                                  · linarith only [h540, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p536_1, u0elo2, u5ehi3]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h464, h466, h534, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h467, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 3) (by simp) with h555 | h555
                                  · linarith only [h0, h555, hlam]
                                  · linarith only [h464, h555, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 3) (by simp) with h558 | h558
                                  · linarith only [h0, h558, hlam]
                                  · linarith only [h465, h558, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h464, h466, h534, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 3) (by simp) with h564 | h564
                                  · linarith only [h201, h564, hlam]
                                  · linarith only [h464, h564, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 3) (by simp) with h567 | h567
                                  · linarith only [h201, h567, hlam]
                                  · linarith only [h465, h567, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h464, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h528, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h531, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h534, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h465, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h529, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h532, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h465, hc34, hlam, hphi, ht0b, ht45, ht5b, p536_1, u0elo2]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                            · linarith only [h462, h466, h533, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
                          · linarith only [h465, h532, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                        · linarith only [h201, h531, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h464, h466, h526, h530, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                    · linarith only [h0, h465, h529, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h464, h528, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
              · rcases m.htr 1 2 4 (by decide) (by decide) with h587 | h587
                · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h589 | h589
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h590 | h590
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h593 | h593
                            · linarith only [h462, h466, h593, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h462, h586, h588, h590, h593, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h201, h465, h592, hlam]
                        · linarith only [h201, h464, h465, h466, h586, h588, h590, h591, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h462, h587, h590, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h0, h465, h589, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h201, h464, h586, h588, hlam]
                · linarith only [h201, h465, h586, h587, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                · linarith only [h586, h602, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h605 | h605
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h606 | h606
                      · linarith only [h462, h466, h586, h604, h606, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
                            · linarith only [h462, h466, h610, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h462, h610, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h465, h609, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                        · linarith only [h201, h464, h466, h608, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi0]
                    · linarith only [h0, h465, h605, hlam]
                  · linarith only [h0, h464, h604, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h617 | h617
            · linarith only [h464, h465, h617, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
              · rcases m.htr 1 2 4 (by decide) (by decide) with h620 | h620
                · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h622 | h622
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                          · linarith only [h201, h465, h625, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h201, h619, h622, h625, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h201, h464, h465, h619, h622, h624, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h462, h620, h623, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h201, h619, h622, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h201, h619, h621, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h201, h619, h620, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h633 | h633
                · linarith only [h619, h633, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h635 | h635
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h636 | h636
                    · linarith only [h462, h464, h465, h619, h636, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                      · linarith only [h462, h617, h635, h636, h638, hc35, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                          · linarith only [h0, h636, h641, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h201, h641, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h201, h464, h640, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                  · linarith only [h0, h464, h635, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h646 | h646
          · rcases m.htr 0 4 5 (by decide) (by decide) with h647 | h647
            · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
              · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
                · rcases m.htr 1 3 4 (by decide) (by decide) with h650 | h650
                  · linarith only [h464, h646, h650, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h201, h648, h650, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h201, h648, h649, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                · linarith only [h648, h654, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h656 | h656
                  · linarith only [h464, h646, h648, h656, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h660 | h660
                        · linarith only [h0, h656, h660, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h201, h660, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h647, h654, h659, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
                    · linarith only [h0, h646, h658, hlam]
            · linarith only [h464, h646, h647, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h666 | h666
            · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
              · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
                · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                        · linarith only [h201, h464, h672, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h201, h667, h669, h672, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h464, h666, h667, h668, h669, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h464, h669, h670, hc03, hc35, hlam, hphi]
                  · linarith only [h201, h667, h669, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h201, h667, h668, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                · linarith only [h667, h679, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
                  · linarith only [h201, h464, h667, h681, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h683 | h683
                    · linarith only [h201, h646, h681, h683, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                        · linarith only [h0, h681, h686, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h201, h686, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h666, h679, h685, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
              · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                · rcases m.htr 1 3 4 (by decide) (by decide) with h692 | h692
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h693 | h693
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h694 | h694
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h695 | h695
                        · linarith only [h201, h464, h695, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h201, h695, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h462, h691, h694, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h201, h464, h692, h693, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h201, h690, h692, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h201, h690, h691, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h702 | h702
                · linarith only [h690, h702, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h704 | h704
                  · linarith only [h201, h464, h690, h704, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h706 | h706
                    · linarith only [h201, h646, h704, h706, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h708 | h708
                      · linarith only [h462, h666, h702, h708, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h710 | h710
                        · linarith only [h201, h464, h710, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h201, h710, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_14_M_LI_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
                      · linarith only [h0, h10, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h10, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h15, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h14, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h21, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h21, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h20, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h26, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h26, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h25, h4, hc12, hlam, hphi, u2elo0]
              · linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
              · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
                · linarith only [h32, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                      · linarith only [h36, h5, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h39 | h39
                          · linarith only [h1, h32, h34, h39, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                            · linarith only [h2, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h34, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h31, h38, h5, hc12, hlam, hphi, u2elo3]
                    · linarith only [h35, h4, h5, hc12, hlam, hphi, u2elo3]
                  · linarith only [h31, h34, h5, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h47 | h47
                · linarith only [h4, h47, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                      · linarith only [h5, h51, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h0, h31, h53, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                          · linarith only [h0, h47, h49, h50, h55, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h2, h57, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h49, h57, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h4, h5, h50, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                      · linarith only [h5, h62, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                        · linarith only [h0, h31, h64, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                          · linarith only [h1, h47, h66, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                            · linarith only [h2, h49, h68, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h0, h49, h5, h61, h70, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                              · linarith only [h0, h5, h61, h70, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h4, h5, h61, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
            · linarith only [h4, h74, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h76 | h76
              · rcases m.htr 0 3 4 (by decide) (by decide) with h77 | h77
                · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                    · linarith only [h4, h79, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h74, h81, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
                          · linarith only [h1, h84, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h4, h77, h79, h84, hc12, hlam, hphi, u2elo2]
                        · linarith only [h74, h76, h83, hc12, hlam, hphi, u2elo3]
                  · linarith only [h74, h76, h78, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                    · linarith only [h4, h90, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h4, h92, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                          · linarith only [h1, h77, h95, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                            · linarith only [h2, h97, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h89, h97, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h4, h76, h94, hc12, hlam, hphi, u2elo2]
                  · linarith only [h74, h76, h89, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                    · linarith only [h104, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                      · linarith only [h0, h106, h76, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h0, h108, h76, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                          · linarith only [h1, h110, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h102, h104, h110, h4, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                    · linarith only [h102, h113, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                      · linarith only [h0, h115, h74, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                        · linarith only [h0, h117, h76, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                          · linarith only [h1, h119, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h102, h113, h119, h4, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                    · linarith only [h123, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                      · linarith only [h0, h125, h74, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h0, h127, h76, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                          · linarith only [h1, h129, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                            · linarith only [h131, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · linarith only [h122, h131, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                    · linarith only [h0, h134, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                      · linarith only [h0, h136, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                        · linarith only [h0, h138, h76, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                          · linarith only [h1, h102, h140, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                            · linarith only [h142, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                              · linarith only [h102, h122, h144, h4, hc02, hlam, hphi, u2elo3]
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
                                      · linarith only [h151, h4, hlam]
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
                                        · linarith only [h160, h2, hlam]
                                        · linarith only [h102, h160, hlam]
                                  · linarith only [h1, h155, hlam]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, p146_1, u0elo0, u4ehi1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h122, h2, hlam, hphi, ht0b, ht45, ht5b, p146_1, u0elo0, u4ehi1]
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
                                  linarith only [h4, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h74, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h76, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h1, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h102, hc12, hc34, hlam, hphi, ht23, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h102, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h102, h122, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h2, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h74, hc12, hlam, hphi, p146_1, u2elo3]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h144, h74, hc03, hc45, hlam, hphi, ht34, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h122, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h3, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h76, hc12, hlam, hphi, p146_1, u2elo4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h4, h76, hc12, hlam, hphi, p146_1, u2elo4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h76, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p146_1, u2elo4, u4ehi0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h186 | h186
          · rcases m.htr 0 2 4 (by decide) (by decide) with h187 | h187
            · rcases m.htr 0 2 5 (by decide) (by decide) with h188 | h188
              · linarith only [h0, h188, h3, hlam]
              · linarith only [h187, h188, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
              · linarith only [h0, h187, h191, h3, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
                · linarith only [h186, h187, h193, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h195 | h195
                  · linarith only [h195, h2, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h198 | h198
                      · linarith only [h187, h198, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
                        · linarith only [h0, h187, h191, h200, h3, hc01, hlam, hphi, ht12, u2elo3]
                        · linarith only [h197, h198, h2, h200, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h186, h187, h197, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h204 | h204
            · linarith only [h186, h204, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h206 | h206
              · linarith only [h186, h2, h206, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 0 4 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h1, h208, h209, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
                    · linarith only [h186, h211, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h1, h204, h211, h213, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                        · linarith only [h0, h1, h206, h208, h215, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · linarith only [h1, h208, h215, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
                  · linarith only [h2, h218, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                    · linarith only [h186, h220, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                      · linarith only [h1, h204, h220, h222, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                        · linarith only [h0, h2, h206, h224, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                        · linarith only [h2, h224, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h227 | h227
        · rcases m.htr 0 2 3 (by decide) (by decide) with h228 | h228
          · rcases m.htr 0 2 4 (by decide) (by decide) with h229 | h229
            · linarith only [h0, h2, h229, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h231 | h231
              · rcases m.htr 0 3 4 (by decide) (by decide) with h232 | h232
                · linarith only [h228, h229, h232, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h229, h236, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h236, hc12, hlam, hphi, u2elo3]
                    · linarith only [h228, h235, hc12, hlam, hphi, u2elo0]
                  · linarith only [h2, h227, h234, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h241 | h241
                · linarith only [h228, h229, h241, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
                      · linarith only [h0, h2, h229, h245, hlam]
                      · linarith only [h0, h2, h244, h245, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h228, h229, h244, hc12, hlam, hphi, u2elo3]
                  · linarith only [h2, h227, h243, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h250 | h250
            · linarith only [h228, h250, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h252 | h252
              · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
                · linarith only [h1, h2, h253, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h255 | h255
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
                    · linarith only [h228, h256, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
                      · linarith only [h250, h252, h255, h258, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                      · linarith only [h1, h2, h256, h258, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h2, h228, h252, h255, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
                · linarith only [h1, h2, h262, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                    · linarith only [h0, h228, h265, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                      · linarith only [h1, h2, h250, h265, h267, hlam]
                      · linarith only [h1, h2, h265, h267, hc12, hlam, hphi, u2elo3]
                  · linarith only [h2, h227, h264, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h271 | h271
          · rcases m.htr 0 2 4 (by decide) (by decide) with h272 | h272
            · linarith only [h0, h2, h272, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
              · linarith only [h0, h227, h272, h274, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
                · linarith only [h271, h272, h276, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h278 | h278
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h280 | h280
                      · linarith only [h0, h272, h280, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h279, h280, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h271, h279, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
                    · linarith only [h0, h2, h278, h284, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h271, h272, h284, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h287 | h287
            · linarith only [h271, h287, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h289 | h289
              · linarith only [h1, h227, h271, h289, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
                · linarith only [h1, h2, h291, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                    · linarith only [h0, h271, h294, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h227, h271, h287, h293, h296, hc01, hlam, hphi, ht12, u2elo2]
                      · linarith only [h1, h2, h294, h296, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                    · linarith only [h271, h299, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
                      · linarith only [h0, h271, h301, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
                      · linarith only [h0, h2, h301, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h304 | h304
      · rcases m.htr 0 1 5 (by decide) (by decide) with h305 | h305
        · rcases m.htr 0 2 3 (by decide) (by decide) with h306 | h306
          · linarith only [h0, h1, h306, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h308 | h308
            · linarith only [h306, h308, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h310 | h310
              · rcases m.htr 0 3 4 (by decide) (by decide) with h311 | h311
                · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                    · linarith only [h306, h313, hc02, hlam, hphi, u2elo1]
                    · linarith only [h1, h304, h312, h313, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h308, h310, h312, hlam]
                · linarith only [h1, h304, h311, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h318 | h318
                · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                    · linarith only [h0, h306, h318, h320, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · linarith only [h1, h304, h319, h320, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                    · linarith only [h0, h306, h323, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1, h323, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h304, h318, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
          · linarith only [h0, h1, h327, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
            · linarith only [h327, h329, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h331 | h331
              · linarith only [h0, h305, h327, h331, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h333 | h333
                · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                  · linarith only [h304, h305, h334, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                    · linarith only [h327, h336, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1, h336, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h304, h333, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h340 | h340
        · rcases m.htr 0 2 3 (by decide) (by decide) with h341 | h341
          · linarith only [h0, h1, h341, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h343 | h343
            · linarith only [h341, h343, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h345 | h345
              · rcases m.htr 0 3 4 (by decide) (by decide) with h346 | h346
                · rcases m.htr 0 4 5 (by decide) (by decide) with h347 | h347
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h348 | h348
                    · linarith only [h341, h345, h348, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1, h348, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h304, h345, h347, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                    · linarith only [h341, h353, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1, h353, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h1, h345, h346, h352, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h357 | h357
                · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h359 | h359
                    · linarith only [h341, h359, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1, h359, hc12, hlam, hphi, u2elo2]
                  · linarith only [h304, h340, h358, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h363 | h363
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                    · linarith only [h0, h1, h357, h364, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h364, hc12, hlam, hphi, u2elo2]
                  · linarith only [h304, h340, h363, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h368 | h368
          · linarith only [h0, h1, h368, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h370 | h370
            · linarith only [h368, h370, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h372 | h372
              · linarith only [h0, h340, h372, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h374 | h374
                · rcases m.htr 0 4 5 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                    · linarith only [h0, h368, h376, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1, h376, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
                    · linarith only [h0, h368, h374, h379, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                    · linarith only [h0, h1, h379, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
                    · linarith only [h0, h1, h374, h383, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h383, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                    · linarith only [h0, h1, h374, h382, h386, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1, h386, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h389 | h389
    · rcases m.htr 0 1 4 (by decide) (by decide) with h390 | h390
      · linarith only [h0, h390, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h392 | h392
        · rcases m.htr 0 2 3 (by decide) (by decide) with h393 | h393
          · rcases m.htr 0 2 4 (by decide) (by decide) with h394 | h394
            · rcases m.htr 0 2 5 (by decide) (by decide) with h395 | h395
              · rcases m.htr 0 3 4 (by decide) (by decide) with h396 | h396
                · linarith only [h0, h389, h396, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h401 | h401
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h402 | h402
                          · linarith only [h389, h390, h396, h400, h402, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h404 | h404
                            · linarith only [h390, h392, h400, h404, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                            · linarith only [h390, h394, h398, h404, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h389, h399, h401, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h389, h399, h400, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h399, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h390, h392, h398, hlam]
              · linarith only [h394, h395, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h412 | h412
              · rcases m.htr 0 3 4 (by decide) (by decide) with h413 | h413
                · linarith only [h0, h389, h394, h413, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h417 | h417
                      · linarith only [h0, h394, h417, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h389, h416, h417, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h416, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h390, h392, h415, hlam]
              · linarith only [h0, h392, h412, hlam]
          · linarith only [h0, h389, h393, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h424 | h424
          · rcases m.htr 0 2 4 (by decide) (by decide) with h425 | h425
            · rcases m.htr 0 2 5 (by decide) (by decide) with h426 | h426
              · rcases m.htr 0 3 4 (by decide) (by decide) with h427 | h427
                · linarith only [h0, h389, h427, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                          · linarith only [h389, h390, h427, h431, h433, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h435 | h435
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h436 | h436
                              · linarith only [h425, h436, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                              · linarith only [h429, h436, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                            · linarith only [h390, h429, h435, hlam]
                        · linarith only [h390, h429, h431, h432, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi4]
                      · linarith only [h0, h389, h430, h431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h430, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                          · linarith only [h389, h427, h446, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                            · linarith only [h389, h390, h429, h443, h444, h448, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h389, h390, h443, h448, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h389, h443, h445, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h389, h425, h443, h444, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h389, h443, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h425, h426, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h455 | h455
              · rcases m.htr 0 3 4 (by decide) (by decide) with h456 | h456
                · linarith only [h0, h389, h456, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
                      · linarith only [h389, h392, h425, h455, h459, h460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h389, h459, h460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h389, h459, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h425, h455, h458, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h465 | h465
                · linarith only [h0, h389, h465, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h469 | h469
                      · linarith only [h0, h425, h469, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h389, h468, h469, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h389, h468, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h474 | h474
                      · linarith only [h425, h474, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h389, h473, h474, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h389, h473, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h389, h424, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h479 | h479
      · linarith only [h0, h479, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h481 | h481
        · rcases m.htr 0 2 3 (by decide) (by decide) with h482 | h482
          · rcases m.htr 0 2 4 (by decide) (by decide) with h483 | h483
            · rcases m.htr 0 2 5 (by decide) (by decide) with h484 | h484
              · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
                · rcases m.htr 0 4 5 (by decide) (by decide) with h486 | h486
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h488 | h488
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h489 | h489
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                            · linarith only [h479, h481, h487, h490, h491, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                            · linarith only [h479, h482, h485, h486, h491, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h389, h481, h482, h485, h486, h490, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                        · linarith only [h0, h482, h485, h489, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi3]
                      · linarith only [h0, h482, h485, h486, h488, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                    · linarith only [h0, h482, h487, hlam]
                  · linarith only [h479, h481, h486, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h503 | h503
                          · linarith only [h389, h485, h500, h503, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h505 | h505
                            · linarith only [h0, h481, h505, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                            · linarith only [h389, h483, h499, h503, h505, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h481, h499, h502, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi4]
                      · linarith only [h389, h481, h499, h500, h501, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                    · linarith only [h0, h482, h500, hlam]
                  · linarith only [h479, h481, h499, hlam]
              · linarith only [h483, h484, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h513 | h513
              · rcases m.htr 0 3 4 (by decide) (by decide) with h514 | h514
                · linarith only [h482, h483, h514, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h516 | h516
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
                      · linarith only [h483, h518, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h481, h516, h518, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                    · linarith only [h0, h481, h516, h517, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h479, h481, h516, hlam]
              · linarith only [h389, h481, h482, h513, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h524 | h524
            · linarith only [h482, h524, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h526 | h526
              · rcases m.htr 0 3 4 (by decide) (by decide) with h527 | h527
                · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                    · linarith only [h482, h529, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h529, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h479, h481, h528, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h533 | h533
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
                    · linarith only [h0, h482, h534, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h481, h533, h534, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h479, h481, h533, hlam]
              · linarith only [h0, h481, h526, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h539 | h539
          · rcases m.htr 0 2 4 (by decide) (by decide) with h540 | h540
            · rcases m.htr 0 2 5 (by decide) (by decide) with h541 | h541
              · rcases m.htr 0 3 4 (by decide) (by decide) with h542 | h542
                · rcases m.htr 0 4 5 (by decide) (by decide) with h543 | h543
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h546 | h546
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h547 | h547
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h549 | h549
                              · linarith only [h540, h549, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                              · linarith only [h542, h543, h549, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                            · linarith only [h389, h542, h543, h544, h548, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
                          · linarith only [h389, h542, h547, hlam]
                        · linarith only [h389, h542, h544, h546, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi3]
                      · linarith only [h389, h542, h543, h544, h545, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                    · linarith only [h0, h539, h544, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h559 | h559
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                            · linarith only [h543, h558, h561, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                              · linarith only [h540, h561, h563, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                              · rcases h0bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, hlam, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h389, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h479, hlam, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h481, hlam, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p565_1, u2elo1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h542, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo1, u4ehi3]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo1, u4ehi0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h540, h543, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo1, u4ehi2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h389, h557, hc01, hlam, hphi, ht12, p565_1, u2elo1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h539, hlam, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h389, h540, h557, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo1, u4ehi2]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h389, h481, h557, hc01, hlam, hphi, ht12, p565_1, u2elo1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h479, h561, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h540, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h542, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h543, hlam, p565_0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h541, hc01, hlam, hphi, ht12, p565_1, u2elo1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h541, hlam, p565_1]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h541, h542, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo1, u4ehi3]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [h0, h541, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p565_1, u2elo1, u4ehi0]
                                · have p565_0 := h565c.1
                                  have p565_1 := h565c.2.1
                                  have p565_2 := h565c.2.2.1
                                  have p565_3 := h565c.2.2.2
                                  linarith only [hlam, p565_0]
                          · linarith only [h389, h542, h560, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h539, h542, h559, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi3]
                      · linarith only [h0, h540, h558, hlam]
                    · linarith only [h0, h539, h557, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h596 | h596
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h598 | h598
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h599 | h599
                          · linarith only [h389, h542, h596, h599, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h601 | h601
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h602 | h602
                              · linarith only [h0, h540, h602, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                              · linarith only [h0, h540, h595, h602, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                            · linarith only [h0, h540, h595, h601, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
                        · linarith only [h0, h541, h598, hlam]
                      · linarith only [h0, h540, h595, h597, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                    · linarith only [h0, h539, h540, h595, h596, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h609 | h609
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h610 | h610
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h611 | h611
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                          · linarith only [h389, h542, h609, h612, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h614 | h614
                            · linarith only [h595, h610, h614, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h616 | h616
                              · linarith only [h540, h612, h614, h616, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases h0bigk with h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h389, hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h479, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h481, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p618_1, u2elo1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, h389, hc01, hlam, hphi, ht12, p618_1, u2elo1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p618_1, u2elo1, u4ehi0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, h481, hc01, hlam, hphi, ht12, p618_1, u2elo1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h389, h612, hc01, hc34, hlam, hphi, ht12, ht23, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h539, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h542, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h542, h595, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, h479, h541, h614, h616, hc01, hc45, hlam, hphi, ht12, p618_1, u2elo1, u4ehi2]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h540, hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h479, h614, hc03, hc45, hlam, hphi, ht34, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h595, hlam, p618_0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, h541, hc01, hlam, hphi, ht12, p618_1, u2elo1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h541, hlam, p618_1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, h389, h541, hc01, hlam, hphi, ht12, p618_1, u2elo1]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [h0, h541, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p618_1, u2elo1, u4ehi0]
                                · have p618_0 := h618c.1
                                  have p618_1 := h618c.2.1
                                  have p618_2 := h618c.2.2.1
                                  have p618_3 := h618c.2.2.2
                                  linarith only [hlam, p618_0]
                        · linarith only [h0, h541, h611, hlam]
                      · linarith only [h0, h610, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h540, h609, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
              · linarith only [h540, h541, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h648 | h648
              · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
                · linarith only [h539, h540, h649, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
                      · linarith only [h540, h653, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h653, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h652, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h540, h648, h651, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h658 | h658
                · linarith only [h539, h540, h658, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h662 | h662
                      · linarith only [h540, h662, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h662, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h539, h661, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                      · linarith only [h540, h667, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h667, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h539, h666, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h671 | h671
            · linarith only [h539, h671, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h673 | h673
              · rcases m.htr 0 3 4 (by decide) (by decide) with h674 | h674
                · rcases m.htr 0 4 5 (by decide) (by decide) with h675 | h675
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
                    · linarith only [h539, h676, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h676, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h671, h673, h675, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h680 | h680
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h681 | h681
                    · linarith only [h539, h681, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h681, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h539, h673, h674, h680, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h685 | h685
                · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h687 | h687
                    · linarith only [h539, h687, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h687, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
                    · linarith only [h539, h690, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h690, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h694 | h694
                    · linarith only [h0, h539, h694, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h694, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h697 | h697
                    · linarith only [h0, h539, h697, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h697, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
