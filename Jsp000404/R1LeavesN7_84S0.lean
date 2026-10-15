import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_R_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h11, h14, h5, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h0, h10, h14, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h0, h10, h13, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h12, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                        · linarith only [h0, h11, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                      · linarith only [h10, h6, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h8, h9, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h0, h3, h5, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · linarith only [h1, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h3, h4, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h2, h27, h3, h31, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                        · linarith only [h0, h28, h3, h30, h33, h35, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
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
                                  linarith only [h30, h33, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u0elo2, u2ehi4]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h3, hc23, hc34, hlam, hphi, p40_1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h3, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 3) (by simp) with h45 | h45
                                  · rcases p40_3 (m.d 1 3) (by simp) with h46 | h46
                                    · linarith only [h0, h46, hlam]
                                    · linarith only [h33, h46, hlam]
                                  · linarith only [h45, hlam, p40_0]
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
                                  linarith only [h0, h37, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u0elo0, u2ehi4]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h31, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h0, h39, hc45, hlam, hphi, ht0b, ht5b, p40_1, u0elo0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h28, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h35, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, h39, hc45, hlam, hphi, ht0b, ht5b, p40_1, u0elo1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, hc34, hlam, hphi, ht23, p40_1, u2ehi2]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h28, hc34, hlam, hphi, ht23, p40_1, u2ehi2]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht23, p40_1, u2ehi2]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 3) (by simp) with h64 | h64
                                  · linarith only [h3, h64, hlam]
                                  · linarith only [h27, h64, hlam]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h27, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h33, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h37, hlam, p40_0]
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
                              · linarith only [h0, h3, h30, h33, h39, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                            · linarith only [h34, h38, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo1]
                          · linarith only [h37, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h31, h33, h34, hc35, hlam, hphi, u5elo4]
                    · linarith only [h28, h33, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h2, h27, h3, h30, hc34, hlam, hphi, ht23, u2ehi1]
              · linarith only [h28, h29, hc24, hlam, hphi, u2ehi2]
            · linarith only [h1, h28, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h1, h27, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h82 | h82
      · linarith only [h1, h82, hc23, hlam, hphi, u2ehi4]
      · linarith only [h82, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h85 | h85
    · rcases m.htr 0 2 5 (by decide) (by decide) with h86 | h86
      · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
        · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
          · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                              · linarith only [h85, h95, h98, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h85, h95, h97, h98, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h97, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h95, h96, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo3]
                        · linarith only [h87, h95, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · linarith only [h90, h94, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h0, h85, h88, h93, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h87, h92, hlam]
                · linarith only [h86, h91, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
              · linarith only [h89, h90, hc24, hlam, hphi, u2ehi2]
            · linarith only [h85, h89, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h87, h88, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
            · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
              · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                        · linarith only [h111, h118, h86, h87, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                              · rcases h3bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h112, h115, h87, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h87, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h112, h115, h122, h87, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 3) (by simp) with h129 | h129
                                  · linarith only [h0, h129, hlam]
                                  · rcases p123_3 (m.d 1 3) (by simp) with h131 | h131
                                    · rcases p123_3 (m.d 2 3) (by simp) with h132 | h132
                                      · linarith only [h112, h132, hlam]
                                      · rcases p123_3 (m.d 3 4) (by simp) with h134 | h134
                                        · linarith only [h115, h134, hlam]
                                        · linarith only [h134, h87, hlam]
                                    · linarith only [h0, h131, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 3) (by simp) with h139 | h139
                                  · linarith only [h0, h139, hlam]
                                  · linarith only [h139, h85, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h111, h112, h86, h87, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u2ehi4]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h111, h115, h87, hlam, p123_2]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h85, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h112, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h118, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h85, hc35, hlam, hphi, ht0b, ht5b, p123_1, u0elo1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h111, h115, h86, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u2ehi4]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h115, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h112, h115, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u2ehi2]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 3) (by simp) with h153 | h153
                                  · linarith only [h153, h87, hlam]
                                  · linarith only [h111, h153, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h111, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h116, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h120, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h122, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                              · linarith only [h118, h122, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h118, h120, h121, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                          · linarith only [h120, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h113, h117, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h111, h116, h87, hc13, hc34, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                        · linarith only [h0, h115, h168, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h172 | h172
                              · rcases h3bigk with h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h0, hlam, p173_1]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h0, h115, hc23, hc34, hlam, hphi, p173_1]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h87, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  rcases p173_3 (m.d 0 3) (by simp) with h178 | h178
                                  · rcases p173_3 (m.d 1 3) (by simp) with h179 | h179
                                    · rcases p173_3 (m.d 2 3) (by simp) with h180 | h180
                                      · linarith only [h180, h85, hlam]
                                      · linarith only [h170, h180, hlam]
                                    · linarith only [h166, h179, hlam]
                                  · linarith only [h178, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h115, hc03, hc34, hlam, hphi, p173_1]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h115, h170, hc34, hlam, hphi, ht23, p173_1, u2ehi4]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h115, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  rcases p173_3 (m.d 0 3) (by simp) with h189 | h189
                                  · linarith only [h0, h189, hlam]
                                  · linarith only [h111, h189, hlam]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h85, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h112, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h168, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h172, h85, hc45, hlam, hphi, ht0b, ht5b, p173_1, u0elo1]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h85, hc34, hlam, hphi, ht23, p173_1, u2ehi2]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p173_1]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht23, p173_1, u2ehi2]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  rcases p173_3 (m.d 0 3) (by simp) with h201 | h201
                                  · linarith only [h201, h87, hlam]
                                  · linarith only [h111, h201, hlam]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h111, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h166, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h170, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [h172, hlam, p173_0]
                                · have p173_0 := h173c.1
                                  have p173_1 := h173c.2.1
                                  have p173_2 := h173c.2.2.1
                                  have p173_3 := h173c.2.2.2
                                  linarith only [hlam, p173_0]
                              · linarith only [h111, h172, h86, h87, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                            · linarith only [h168, h170, h171, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                          · linarith only [h170, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h113, h167, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h0, h111, h166, hlam]
                · linarith only [h114, h86, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
              · linarith only [h112, h113, hc24, hlam, hphi, u2ehi2]
            · linarith only [h112, h85, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · linarith only [h111, h85, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
      · linarith only [h86, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h219 | h219
      · linarith only [h219, h85, hc23, hlam, hphi, u2ehi4]
      · linarith only [h219, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_10_12_13_25_L_R_L_I_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h10, h4, hc23, hlam, hphi, u3elo0]
                    · linarith only [h3, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h8, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h5, h7, hlam]
                  · linarith only [h15, h4, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h18, h20, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                    · linarith only [h20, h3, hc23, hlam, hphi, u3elo0]
                  · linarith only [h19, h4, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h18, h24, h5, hlam]
                  · linarith only [h24, h4, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                · linarith only [h28, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                        · linarith only [h2, h27, h28, h32, h33, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                          · linarith only [h27, h28, h31, h33, h35, hlam]
                          · rcases h2bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              rcases p37_3 (m.d 0 2) (by simp) with h39 | h39
                              · rcases p37_3 (m.d 1 2) (by simp) with h40 | h40
                                · linarith only [h0, h40, hlam]
                                · rcases p37_3 (m.d 2 3) (by simp) with h42 | h42
                                  · linarith only [h2, h42, hlam]
                                  · linarith only [h42, h5, hlam]
                              · linarith only [h0, h39, hlam]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h0, h27, h28, h32, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, h27, h28, h32, hlam, p37_2]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h27, h28, h31, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h0, hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h5, hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h28, h31, h33, hc34, hc45, hlam, hphi, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h28, hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht23, p37_1, u3elo0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              rcases p37_3 (m.d 0 2) (by simp) with h57 | h57
                              · rcases p37_3 (m.d 1 2) (by simp) with h58 | h58
                                · linarith only [h5, h58, hlam]
                                · linarith only [h27, h58, hlam]
                              · linarith only [h0, h27, h57, hc01, hlam, hphi, u0ehi1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p37_1, u3elo0, u5ehi2]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, h27, h28, h32, hlam, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h27, hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h31, hlam, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [hlam, p37_0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h33, hlam, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, h32, hlam, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h2, h27, h31, h32, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p37_1, u3elo0]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [h32, hlam, p37_1]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              rcases p37_3 (m.d 0 2) (by simp) with h71 | h71
                              · rcases p37_3 (m.d 1 2) (by simp) with h72 | h72
                                · linarith only [h28, h72, hlam]
                                · linarith only [h27, h72, hlam]
                              · linarith only [h0, h2, h27, h32, h71, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                            · have p37_0 := h37c.1
                              have p37_1 := h37c.2.1
                              have p37_2 := h37c.2.2.1
                              have p37_3 := h37c.2.2.2
                              linarith only [hlam, p37_0]
                      · linarith only [h27, h30, h31, h32, h5, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h31, h5, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h30, h4, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                · linarith only [h5, h80, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                          · linarith only [h2, h83, h86, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                          · rcases h2bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              rcases p88_3 (m.d 0 2) (by simp) with h90 | h90
                              · rcases p88_3 (m.d 1 2) (by simp) with h91 | h91
                                · linarith only [h0, h91, hlam]
                                · rcases p88_3 (m.d 2 3) (by simp) with h93 | h93
                                  · linarith only [h2, h93, hlam]
                                  · linarith only [h5, h93, hlam]
                              · linarith only [h0, h90, hlam]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h83, h85, h86, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p88_1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h0, h85, h86, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p88_1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              rcases p88_3 (m.d 0 2) (by simp) with h99 | h99
                              · rcases p88_3 (m.d 1 2) (by simp) with h100 | h100
                                · linarith only [h0, h100, hlam]
                                · rcases p88_3 (m.d 2 3) (by simp) with h102 | h102
                                  · linarith only [h102, h2, hlam]
                                  · linarith only [h102, h84, hlam]
                              · linarith only [h99, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h0, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h5, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h27, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h80, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht23, p88_1, u3elo0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, h85, h86, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p88_1, u3elo0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p88_1, u3elo0, u5ehi2]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht12, p88_1, u0ehi1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, h83, hc12, hlam, hphi, ht23, p88_1, u3elo0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h83, hlam, p88_1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h2, h80, h83, hc12, hlam, hphi, ht23, p88_1, u3elo0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p88_1, u0ehi1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h84, hc12, hlam, hphi, ht23, p88_1, u3elo2]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h84, hlam, p88_1]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [h85, hlam, p88_0]
                            · have p88_0 := h88c.1
                              have p88_1 := h88c.2.1
                              have p88_2 := h88c.2.2.1
                              have p88_3 := h88c.2.2.2
                              linarith only [hlam, p88_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                          · linarith only [h126, h3, h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · rcases h2bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              rcases p128_3 (m.d 0 2) (by simp) with h130 | h130
                              · rcases p128_3 (m.d 1 2) (by simp) with h131 | h131
                                · linarith only [h0, h131, hlam]
                                · rcases p128_3 (m.d 2 3) (by simp) with h133 | h133
                                  · linarith only [h133, h2, hlam]
                                  · linarith only [h133, h5, hlam]
                              · linarith only [h0, h130, hlam]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, h5, h82, hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi3]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              rcases p128_3 (m.d 0 2) (by simp) with h138 | h138
                              · rcases p128_3 (m.d 1 2) (by simp) with h139 | h139
                                · linarith only [h0, h139, hlam]
                                · rcases p128_3 (m.d 2 3) (by simp) with h141 | h141
                                  · linarith only [h141, h2, hlam]
                                  · linarith only [h141, h83, hlam]
                              · linarith only [h138, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              rcases p128_3 (m.d 0 2) (by simp) with h145 | h145
                              · rcases p128_3 (m.d 1 2) (by simp) with h146 | h146
                                · linarith only [h0, h146, hlam]
                                · rcases p128_3 (m.d 2 3) (by simp) with h148 | h148
                                  · linarith only [h148, h2, hlam]
                                  · linarith only [h148, h84, hlam]
                              · linarith only [h145, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h0, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h5, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h27, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h80, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h2, hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, p128_1, u3elo2]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h2, h27, hc12, hlam, hphi, ht23, p128_1, u3elo0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p128_1, u3elo0, u5ehi2]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h85, hc02, hc45, hlam, hphi, ht23, ht34, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h85, hc12, hc45, hlam, hphi, ht23, ht34, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h83, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h85, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h2, h84, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h2, h84, hc12, hlam, hphi, ht23, p128_1, u3elo0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h84, hlam, p128_1]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [h2, h27, h84, hc12, hlam, hphi, ht23, p128_1, u3elo0]
                            · have p128_0 := h128c.1
                              have p128_1 := h128c.2.1
                              have p128_2 := h128c.2.2.1
                              have p128_3 := h128c.2.2.2
                              linarith only [hlam, p128_0]
                      · linarith only [h5, h82, h84, hlam]
                    · linarith only [h5, h82, h83, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h4, h82, hc13, hlam, hphi, u3elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h179 | h179
    · rcases m.htr 0 2 3 (by decide) (by decide) with h180 | h180
      · rcases m.htr 0 3 4 (by decide) (by decide) with h181 | h181
        · rcases m.htr 0 3 5 (by decide) (by decide) with h182 | h182
          · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
            · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
              · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                  · linarith only [h0, h179, h186, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h182, h186, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h185, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h179, h182, h184, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h0, h179, h182, h183, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h182, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h181, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h0, h180, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo2]
    · linarith only [h179, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_12_13_25_L_R_L_I_L_R_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
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
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h7, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h13, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h3, h5, h6, hc24, hlam, hphi, ht45, u5elo0]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h1, h19, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h18, h19, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
              · linarith only [h1, h22, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                        · rcases h2bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            rcases p29_3 (m.d 0 2) (by simp) with h31 | h31
                            · rcases p29_3 (m.d 1 2) (by simp) with h32 | h32
                              · linarith only [h0, h32, hlam]
                              · rcases p29_3 (m.d 2 3) (by simp) with h34 | h34
                                · linarith only [h1, h34, hlam]
                                · linarith only [h34, h4, hlam]
                            · linarith only [h0, h31, hlam]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h24, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi3]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h28, hc01, hlam, hphi, ht0b, ht5b, p29_1, u5ehi9]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            rcases p29_3 (m.d 0 2) (by simp) with h40 | h40
                            · rcases p29_3 (m.d 1 2) (by simp) with h41 | h41
                              · linarith only [h0, h41, hlam]
                              · rcases p29_3 (m.d 2 3) (by simp) with h43 | h43
                                · linarith only [h1, h43, hlam]
                                · linarith only [h27, h43, hlam]
                            · linarith only [h40, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h4, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h18, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h22, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h1, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            rcases p29_3 (m.d 0 2) (by simp) with h53 | h53
                            · rcases p29_3 (m.d 1 2) (by simp) with h54 | h54
                              · linarith only [h54, hlam, p29_0]
                              · rcases p29_3 (m.d 2 3) (by simp) with h56 | h56
                                · rcases p29_3 (m.d 2 4) (by simp) with h57 | h57
                                  · linarith only [h26, h57, hlam]
                                  · linarith only [h18, h57, hlam]
                                · linarith only [h56, hlam, p29_0]
                            · linarith only [h0, h53, hlam]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h28, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p29_1, u5ehi9]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h1, h22, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h2, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            rcases p29_3 (m.d 0 2) (by simp) with h66 | h66
                            · rcases p29_3 (m.d 1 2) (by simp) with h67 | h67
                              · linarith only [h67, hlam, p29_0]
                              · rcases p29_3 (m.d 2 3) (by simp) with h69 | h69
                                · rcases p29_3 (m.d 2 4) (by simp) with h70 | h70
                                  · rcases p29_3 (m.d 2 5) (by simp) with h71 | h71
                                    · linarith only [h28, h71, hlam]
                                    · linarith only [h22, h71, hlam]
                                  · linarith only [h70, hlam, p29_0]
                                · linarith only [h4, h69, hlam]
                            · linarith only [h0, h66, hlam]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h26, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h2, h22, h25, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi4]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h3, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p29_1, u5elo2]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h27, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h28, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                        · linarith only [h18, h28, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h25, h27, hlam, hphi, ht34, ht45, u3ehi2, u5elo1]
                    · linarith only [h24, h26, h4, hlam]
                  · linarith only [h24, h25, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                  · linarith only [h24, h89, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h89, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h93 | h93
        · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
          · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
            · linarith only [h0, h2, h95, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
              · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                · linarith only [h94, h95, h98, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                  · linarith only [h100, h98, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h100, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h94, h97, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
          · linarith only [h1, h2, h94, hc12, hc24, hlam, hphi]
        · linarith only [h1, h93, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
      · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
        · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
          · linarith only [h1, h106, h108, hc12, hlam, hphi, ht01, u0ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
              · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h0, h1, h110, h116, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                        · linarith only [h114, h116, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h0, h1, h110, h114, h115, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h114, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h113, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · linarith only [h108, h110, h112, hlam]
              · linarith only [h110, h111, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h106, h110, hc12, hc23, hlam, hphi]
        · linarith only [h106, h107, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h126 | h126
        · rcases m.htr 1 2 3 (by decide) (by decide) with h127 | h127
          · linarith only [h1, h126, h127, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
            · linarith only [h0, h106, h129, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
              · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                        · rcases h2bigk with h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h131, h135, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h1, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h106, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h106, h134, h135, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h0, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h127, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h129, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h0, h135, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p137_1, u0ehi1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h131, h135, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h106, h126, h135, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            rcases p137_3 (m.d 0 2) (by simp) with h152 | h152
                            · linarith only [h1, h152, hlam]
                            · linarith only [h126, h152, hlam]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h0, h131, h135, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h131, h135, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p137_1, u3ehi4]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h134, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            rcases p137_3 (m.d 0 2) (by simp) with h159 | h159
                            · linarith only [h106, h159, hlam]
                            · linarith only [h126, h159, hlam]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h126, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h131, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h135, hlam, p137_1]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [h136, hlam, p137_0]
                          · have p137_0 := h137c.1
                            have p137_1 := h137c.2.1
                            have p137_2 := h137c.2.2.1
                            have p137_3 := h137c.2.2.2
                            linarith only [hlam, p137_0]
                        · linarith only [h0, h106, h131, h135, h136, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                      · linarith only [h1, h135, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
                    · linarith only [h1, h134, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h132, h133, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h132, h171, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h171, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h1, h126, h131, hc12, hc23, hlam, hphi]
        · linarith only [h126, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h176 | h176
    · rcases m.htr 0 2 4 (by decide) (by decide) with h177 | h177
      · rcases m.htr 0 2 5 (by decide) (by decide) with h178 | h178
        · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
          · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
            · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
              · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                        · rcases h2bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h0, hlam, p187_1]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h184, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1, u3ehi3]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h0, h186, hc12, hlam, hphi, ht01, ht0b, ht5b, p187_1, u5ehi9]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            rcases p187_3 (m.d 0 2) (by simp) with h192 | h192
                            · rcases p187_3 (m.d 1 2) (by simp) with h193 | h193
                              · rcases p187_3 (m.d 2 3) (by simp) with h194 | h194
                                · linarith only [h176, h194, hlam]
                                · linarith only [h185, h194, hlam]
                              · linarith only [h181, h193, hlam]
                            · linarith only [h192, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p187_1, u0ehi1]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h184, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p187_1, u3ehi3]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h186, hc12, hlam, hphi, ht01, ht0b, ht5b, p187_1, u5ehi9]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            rcases p187_3 (m.d 0 2) (by simp) with h203 | h203
                            · linarith only [h0, h203, hlam]
                            · linarith only [h178, h203, hlam]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h176, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h179, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h176, h186, hc02, hlam, hphi, ht0b, ht5b, p187_1, u5ehi9]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h0, h176, hc12, hlam, hphi, ht01, ht0b, ht5b, p187_1, u5ehi7]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h177, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h180, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h184, hlam, p187_1]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h0, h177, h185, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p187_1, u3ehi4]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h178, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h181, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h185, hlam, p187_1]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [h186, hlam, p187_0]
                          · have p187_0 := h187c.1
                            have p187_1 := h187c.2.1
                            have p187_2 := h187c.2.2.1
                            have p187_3 := h187c.2.2.2
                            linarith only [hlam, p187_0]
                        · linarith only [h184, h186, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h185, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h182, h184, h223, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h223, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
                  · linarith only [h183, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                  · linarith only [h182, h227, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h227, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h0, h181, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
            · linarith only [h0, h177, h180, hc02, hlam, hphi, u0ehi0]
          · linarith only [h0, h179, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h176, h178, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h234 | h234
        · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
          · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
            · linarith only [h176, h177, h236, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h236, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h176, h235, hc02, hlam, hphi, u0ehi0]
        · linarith only [h176, h234, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h241 | h241
      · rcases m.htr 0 2 5 (by decide) (by decide) with h242 | h242
        · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
          · linarith only [h0, h176, h243, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h243, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h242, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h247 | h247
        · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
          · linarith only [h0, h176, h248, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h248, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h247, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]

theorem r1l7_10_12_13_25_L_R_L_R_L_I_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h10, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h6, h9, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h17, h5, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h19, h3, h4, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h19, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                    · linarith only [h16, h6, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
              · linarith only [h25, h5, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h27, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h27, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h4, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                      · linarith only [h1, h30, h36, h4, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                        · linarith only [h0, h30, h38, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h38, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                    · linarith only [h30, h33, h35, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo4]
                · linarith only [h31, h32, hc25, hlam, hphi, u2ehi3]
              · linarith only [h30, h31, hc24, hlam, hphi, u2ehi2]
            · linarith only [h3, h30, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
          · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
            · linarith only [h0, h3, h46, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
              · linarith only [h0, h3, h48, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h3, h50, hc23, hlam, hphi, u2ehi4]
                · linarith only [h50, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
            · linarith only [h0, h3, h45, h53, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
              · linarith only [h0, h3, h45, h55, hc34, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                · linarith only [h0, h3, h45, h57, hc34, hlam, hphi, ht23, u2ehi4]
                · linarith only [h57, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h60 | h60
        · rcases m.htr 0 3 4 (by decide) (by decide) with h61 | h61
          · linarith only [h1, h2, h61, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
            · linarith only [h0, h2, h63, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h0, h2, h60, h63, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h66 | h66
          · linarith only [h1, h2, h66, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
            · linarith only [h0, h60, h66, h68, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
              · linarith only [h1, h2, h68, h70, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h1, h2, h68, h70, hc24, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
      · rcases m.htr 0 2 3 (by decide) (by decide) with h74 | h74
        · linarith only [h0, h1, h74, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
          · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
            · linarith only [h74, h77, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h1, h77, hc23, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h76, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h81 | h81
        · linarith only [h0, h1, h81, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h83 | h83
          · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
            · linarith only [h0, h1, h81, h84, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
            · linarith only [h0, h1, h84, hc23, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h83, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h88 | h88
    · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
      · rcases m.htr 0 2 3 (by decide) (by decide) with h90 | h90
        · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
          · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h0, h88, h95, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h93, h96, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h0, h88, h91, h92, h95, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h94, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h88, h92, h93, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h92, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
            · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                  · linarith only [h106, h88, h91, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h0, h108, h89, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h104, h108, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h0, h105, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h103, h104, h88, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h103, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h88, h90, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h115 | h115
        · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
          · linarith only [h116, h88, h89, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
            · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
              · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                  · linarith only [h116, h119, h121, h88, h89, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h118, h121, h88, h89, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h118, h119, h120, h88, h89, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h118, h119, h88, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h118, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h115, h88, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h128 | h128
      · rcases m.htr 0 2 3 (by decide) (by decide) with h129 | h129
        · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
          · rcases m.htr 1 2 3 (by decide) (by decide) with h131 | h131
            · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
              · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                    · linarith only [h128, h131, h135, h88, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · linarith only [h132, h135, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h128, h132, h134, h88, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h128, h131, h132, h133, h88, hc25, hlam, hphi, u2ehi3]
              · linarith only [h131, h132, h88, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h128, h129, h131, hc02, hlam, hphi, u0ehi3]
          · linarith only [h128, h130, h88, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
          · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
            · linarith only [h0, h128, h129, h144, hc12, hlam, hphi, ht01, u0ehi3]
            · linarith only [h0, h128, h144, hc23, hlam, hphi, ht01, ht12, u0ehi3]
          · linarith only [h0, h128, h129, h143, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
        · rcases m.htr 0 3 4 (by decide) (by decide) with h149 | h149
          · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
            · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
              · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 3 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                          · linarith only [h148, h155, h157, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases h3bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h88, hlam, p159_1]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h0, h148, h156, hc12, hlam, hphi, ht01, ht0b, ht5b, p159_1, u5ehi8]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              rcases p159_3 (m.d 0 3) (by simp) with h163 | h163
                              · rcases p159_3 (m.d 1 3) (by simp) with h164 | h164
                                · rcases p159_3 (m.d 2 3) (by simp) with h165 | h165
                                  · linarith only [h148, h165, hlam]
                                  · linarith only [h155, h165, hlam]
                                · linarith only [h153, h164, hlam]
                              · linarith only [h163, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              rcases p159_3 (m.d 0 3) (by simp) with h170 | h170
                              · rcases p159_3 (m.d 1 3) (by simp) with h171 | h171
                                · rcases p159_3 (m.d 2 3) (by simp) with h172 | h172
                                  · linarith only [h148, h172, hlam]
                                  · linarith only [h156, h172, hlam]
                                · linarith only [h171, h88, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo3]
                              · linarith only [h170, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hc13, hlam, hphi, ht01, p159_1, u0ehi2]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h150, h156, hc12, hlam, hphi, ht01, ht0b, ht5b, p159_1, u5ehi8]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              rcases p159_3 (m.d 0 3) (by simp) with h180 | h180
                              · linarith only [h180, h88, hlam]
                              · linarith only [h149, h180, hlam]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              rcases p159_3 (m.d 0 3) (by simp) with h183 | h183
                              · linarith only [h183, h88, hlam]
                              · linarith only [h0, h128, h148, h149, h156, h183, hc12, hlam, hphi, ht01, u0ehi0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h148, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h150, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              rcases p159_3 (m.d 0 3) (by simp) with h189 | h189
                              · rcases p159_3 (m.d 1 3) (by simp) with h190 | h190
                                · rcases p159_3 (m.d 2 3) (by simp) with h191 | h191
                                  · rcases p159_3 (m.d 3 4) (by simp) with h192 | h192
                                    · linarith only [h192, hlam, p159_0]
                                    · rcases p159_3 (m.d 3 5) (by simp) with h194 | h194
                                      · linarith only [h156, h194, hlam]
                                      · linarith only [h157, h194, hlam]
                                  · linarith only [h191, hlam, p159_0]
                                · linarith only [h153, h190, hlam]
                              · linarith only [h149, h189, hlam]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h0, h148, hc12, hlam, hphi, ht01, ht0b, ht5b, p159_1, u5ehi8]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h149, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h153, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h155, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h157, hlam, p159_1]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p159_1, u0ehi2]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hc13, hlam, hphi, ht34, ht45, p159_1, u5elo3]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [h156, hlam, p159_0]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hc34, hlam, hphi, ht45, p159_1, u5elo3]
                            · have p159_0 := h159c.1
                              have p159_1 := h159c.2.1
                              have p159_2 := h159c.2.2.1
                              have p159_3 := h159c.2.2.2
                              linarith only [hlam, p159_0]
                        · linarith only [h156, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h212 | h212
                        · linarith only [h149, h155, h212, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h212, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                    · linarith only [h128, h154, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                  · linarith only [h0, h148, h149, h153, h88, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h152, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
              · linarith only [h150, h151, h88, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h148, h150, hc02, hlam, hphi, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                  · linarith only [h149, h220, h223, hc12, hlam, hphi, ht01, u0ehi2]
                  · linarith only [h223, h88, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h221, h222, hc25, hlam, hphi, u2ehi3]
              · linarith only [h220, h221, h88, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h148, h220, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h229 | h229
          · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
            · linarith only [h148, h230, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h230, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
            · linarith only [h0, h148, h233, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h233, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
