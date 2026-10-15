import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LI_L_0_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h3ehi := hb3.1
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
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h13, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h20, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h20, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                      · linarith only [h0, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h23, h4, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 0 2 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
                · rcases m.htr 0 3 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                      · linarith only [h33, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                            · linarith only [h1, h37, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h30, h37, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h29, h36, hc12, hlam, hphi, u2elo0]
                        · linarith only [h28, h35, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                      · linarith only [h4, h42, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                            · linarith only [h1, h46, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h29, h30, h32, h4, h46, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · linarith only [h29, h4, h45, hc12, hlam, hphi, u2elo2]
                        · linarith only [h28, h4, h44, hc12, hlam, hphi, u2elo2]
                  · linarith only [h30, h31, hc35, hlam, hphi, u3ehi3]
                · linarith only [h28, h30, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h53 | h53
                · rcases m.htr 0 3 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h28, h29, h55, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                      · linarith only [h4, h57, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h0, h29, h60, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                            · linarith only [h1, h62, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h53, h62, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h28, h4, h59, hc12, hlam, hphi, u2elo2]
                  · linarith only [h53, h54, hc35, hlam, hphi, u3ehi3]
                · linarith only [h28, h4, h53, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
              · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
                · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                      · linarith only [h0, h72, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                        · linarith only [h0, h28, h74, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                            · linarith only [h1, h77, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h69, h77, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h28, h68, h76, hc12, hlam, hphi, u2elo3]
                    · linarith only [h28, h68, h71, hlam]
                  · linarith only [h69, h70, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h83 | h83
                  · linarith only [h69, h83, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h4, h68, h83, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h86 | h86
                · rcases m.htr 0 3 5 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h89, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                        · linarith only [h0, h28, h91, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                          · linarith only [h0, h68, h93, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                            · linarith only [h1, h95, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h86, h95, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                      · linarith only [h0, h28, h4, h98, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                        · linarith only [h0, h100, h28, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h0, h102, h68, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                            · linarith only [h1, h104, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h104, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h86, h87, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h108 | h108
                  · linarith only [h108, h86, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                      · linarith only [h0, h111, h28, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                        · linarith only [h0, h113, h28, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h0, h115, h68, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                            · linarith only [h1, h117, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                              · linarith only [h1, h108, h119, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                                  · linarith only [h1, h122, h86, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                                    · linarith only [h1, h108, h122, h124, hc34, hlam, hphi, u3ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                                      · rcases h0bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          rcases p127_3 (m.d 0 1) (by simp) with h129 | h129
                                          · rcases p127_3 (m.d 0 2) (by simp) with h130 | h130
                                            · linarith only [h0, h130, hlam]
                                            · rcases p127_3 (m.d 0 3) (by simp) with h132 | h132
                                              · linarith only [h1, h132, hlam]
                                              · linarith only [h132, h4, hlam]
                                          · linarith only [h0, h129, hlam]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p127_1, u0elo0, u3ehi1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h1, h108, h110, hlam, hphi, ht0b, ht34, ht45, ht5b, p127_1, u0elo0, u3ehi1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h1, h108, hlam, hphi, ht0b, ht34, ht45, ht5b, p127_1, u0elo0, u3ehi1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h0, hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h4, hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h28, hlam, p127_1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h68, hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h1, hlam, p127_1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h0, h124, h126, h4, hc12, hc34, hlam, hphi, ht23, p127_1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h86, hlam, p127_1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h108, hlam, p127_1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h2, hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h0, h28, hc12, hlam, hphi, p127_1, u2elo3]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h28, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p127_1, u2elo3, u3ehi0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h0, h28, h68, hc12, hlam, hphi, p127_1, u2elo3]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h3, hlam, p127_0]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h0, h68, hc12, hlam, hphi, p127_1, u2elo4]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h1, h68, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p127_1, u2elo4, u3ehi1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [h110, hlam, p127_1]
                                        · have p127_0 := h127c.1
                                          have p127_1 := h127c.2.1
                                          have p127_2 := h127c.2.2.1
                                          have p127_3 := h127c.2.2.2
                                          linarith only [hlam, p127_0]
                                      · linarith only [h121, h126, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · linarith only [h110, h113, h121, h28, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                      · linarith only [h0, h161, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
                        · linarith only [h0, h163, h28, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h0, h165, h68, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
                            · linarith only [h1, h167, h86, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                              · linarith only [h1, h108, h169, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                                · linarith only [h1, h110, h171, h2, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                                  · linarith only [h1, h173, h86, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                                    · linarith only [h1, h108, h173, h175, hc34, hlam, hphi, u3ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                                      · linarith only [h1, h110, h177, h86, hc34, hlam, hphi, u3ehi1]
                                      · linarith only [h173, h177, h4, hc02, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h180 | h180
          · rcases m.htr 0 2 4 (by decide) (by decide) with h181 | h181
            · rcases m.htr 0 2 5 (by decide) (by decide) with h182 | h182
              · linarith only [h0, h182, h3, hlam]
              · linarith only [h180, h182, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h180, h181, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h186 | h186
            · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
              · linarith only [h0, h180, h187, h3, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
                · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
                  · linarith only [h1, h190, h3, hlam]
                  · linarith only [h189, h190, hc35, hlam, hphi, u3ehi3]
                · linarith only [h180, h186, h189, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h194 | h194
              · linarith only [h0, h180, h194, h3, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 0 3 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h1, h197, h3, hlam]
                  · linarith only [h196, h197, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
                  · linarith only [h196, h200, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h202 | h202
                    · linarith only [h2, h202, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
                      · linarith only [h180, h204, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h0, h186, h206, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h208 | h208
                          · linarith only [h0, h1, h194, h208, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                          · linarith only [h1, h208, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h211 | h211
        · rcases m.htr 0 2 3 (by decide) (by decide) with h212 | h212
          · rcases m.htr 0 2 4 (by decide) (by decide) with h213 | h213
            · linarith only [h0, h2, h213, hlam]
            · linarith only [h212, h213, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h216 | h216
            · linarith only [h0, h2, h212, h216, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h218 | h218
              · rcases m.htr 0 3 4 (by decide) (by decide) with h219 | h219
                · linarith only [h1, h2, h219, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h219, h221, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h212, h218, h221, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h224 | h224
                · linarith only [h1, h2, h224, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h226 | h226
                  · linarith only [h224, h226, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
                      · linarith only [h212, h229, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                        · linarith only [h0, h1, h2, h216, h231, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h1, h2, h231, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                    · linarith only [h1, h2, h228, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h235 | h235
          · rcases m.htr 0 2 4 (by decide) (by decide) with h236 | h236
            · linarith only [h0, h2, h236, hlam]
            · linarith only [h235, h236, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
            · linarith only [h0, h2, h235, h239, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
              · linarith only [h1, h211, h235, h241, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
                · linarith only [h1, h2, h243, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h245 | h245
                  · linarith only [h243, h245, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                      · linarith only [h235, h248, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                        · linarith only [h0, h211, h235, h239, h247, h250, hc01, hlam, hphi, ht12, u2elo2]
                        · linarith only [h1, h2, h250, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                    · linarith only [h1, h2, h247, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h254 | h254
      · rcases m.htr 0 1 5 (by decide) (by decide) with h255 | h255
        · rcases m.htr 0 2 3 (by decide) (by decide) with h256 | h256
          · linarith only [h0, h1, h256, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h258 | h258
            · rcases m.htr 0 2 5 (by decide) (by decide) with h259 | h259
              · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
                · rcases m.htr 0 3 5 (by decide) (by decide) with h261 | h261
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h262 | h262
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
                      · linarith only [h256, h263, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h263, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h266, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h266, hc12, hlam, hphi, u2elo2]
                  · linarith only [h260, h261, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h254, h260, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
                · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h273 | h273
                    · linarith only [h258, h259, h273, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                      · linarith only [h0, h275, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h275, hc12, hlam, hphi, u2elo2]
                  · linarith only [h271, h272, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h258, h259, h271, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 0 3 4 (by decide) (by decide) with h281 | h281
                · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h283 | h283
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
                      · linarith only [h0, h284, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h284, hc12, hlam, hphi, u2elo2]
                    · linarith only [h258, h280, h283, hlam]
                  · linarith only [h281, h282, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h254, h281, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h290 | h290
                · rcases m.htr 0 3 5 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h293 | h293
                      · linarith only [h0, h293, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h293, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                      · linarith only [h0, h256, h296, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · linarith only [h0, h1, h296, hc12, hlam, hphi, u2elo2]
                  · linarith only [h290, h291, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h254, h290, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h301 | h301
          · linarith only [h0, h1, h301, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h303 | h303
            · rcases m.htr 0 2 5 (by decide) (by decide) with h304 | h304
              · linarith only [h0, h255, h301, h304, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
                · rcases m.htr 0 3 5 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h308 | h308
                    · linarith only [h0, h255, h301, h303, h308, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h301, h310, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h310, hc12, hlam, hphi, u2elo2]
                  · linarith only [h306, h307, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h303, h306, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h315 | h315
              · linarith only [h254, h255, h303, h315, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h317 | h317
                · rcases m.htr 0 3 5 (by decide) (by decide) with h318 | h318
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h319 | h319
                    · linarith only [h254, h255, h319, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
                      · linarith only [h0, h321, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h321, hc12, hlam, hphi, u2elo2]
                  · linarith only [h317, h318, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h254, h317, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h326 | h326
        · rcases m.htr 0 2 3 (by decide) (by decide) with h327 | h327
          · linarith only [h0, h1, h327, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
            · linarith only [h0, h254, h327, h329, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h331 | h331
              · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
                · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h335 | h335
                      · linarith only [h0, h327, h335, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h335, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h254, h331, h334, hlam]
                  · linarith only [h332, h333, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h340 | h340
                  · linarith only [h332, h340, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h1, h331, h340, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h343 | h343
                · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                      · linarith only [h0, h346, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h346, hc12, hlam, hphi, u2elo2]
                    · linarith only [h254, h326, h345, hlam]
                  · linarith only [h343, h344, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
                  · linarith only [h343, h351, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h326, h351, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h354 | h354
          · linarith only [h0, h1, h354, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
            · linarith only [h0, h254, h356, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h358 | h358
              · linarith only [h0, h326, h358, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h360 | h360
                · rcases m.htr 0 3 5 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                      · linarith only [h0, h354, h363, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h363, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h366 | h366
                      · linarith only [h0, h354, h366, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                      · linarith only [h0, h1, h366, hc12, hlam, hphi, u2elo2]
                  · linarith only [h360, h361, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h370 | h370
                  · linarith only [h360, h370, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h354, h373, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h373, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
                      · linarith only [h0, h376, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h0, h1, h376, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h379 | h379
    · linarith only [h0, h379, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h381 | h381
      · rcases m.htr 0 1 5 (by decide) (by decide) with h382 | h382
        · rcases m.htr 0 2 3 (by decide) (by decide) with h383 | h383
          · rcases m.htr 0 2 4 (by decide) (by decide) with h384 | h384
            · rcases m.htr 0 2 5 (by decide) (by decide) with h385 | h385
              · rcases m.htr 0 3 4 (by decide) (by decide) with h386 | h386
                · rcases m.htr 0 3 5 (by decide) (by decide) with h387 | h387
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                            · linarith only [h379, h381, h389, h392, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                            · linarith only [h379, h383, h386, h392, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h381, h387, h388, h391, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi4]
                        · linarith only [h379, h381, h387, h388, h389, h390, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
                      · linarith only [h0, h381, h387, h388, h389, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                            · linarith only [h379, h381, h398, h401, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                            · linarith only [h379, h383, h386, h401, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h379, h398, h400, hc01, hlam, hphi, ht12, u2elo4]
                        · linarith only [h379, h382, h386, h388, h398, h399, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                      · linarith only [h0, h382, h386, h388, h398, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h386, h387, hc35, hlam, hphi, u3ehi3]
                · linarith only [h379, h381, h386, hlam]
              · linarith only [h383, h385, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h383, h384, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h411 | h411
            · rcases m.htr 0 2 5 (by decide) (by decide) with h412 | h412
              · rcases m.htr 0 3 4 (by decide) (by decide) with h413 | h413
                · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                      · linarith only [h0, h383, h416, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h381, h414, h415, h416, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                      · linarith only [h0, h383, h419, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h382, h413, h415, h419, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h413, h414, hc35, hlam, hphi, u3ehi3]
                · linarith only [h379, h381, h413, hlam]
              · linarith only [h0, h382, h412, hlam]
            · linarith only [h0, h381, h411, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h426 | h426
          · rcases m.htr 0 2 4 (by decide) (by decide) with h427 | h427
            · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
              · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
                · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h431 | h431
                    · linarith only [h381, h382, h431, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
                            · linarith only [h379, h381, h433, h436, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                            · linarith only [h379, h426, h429, h436, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h381, h429, h435, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                        · linarith only [h379, h381, h429, h433, h434, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                      · linarith only [h0, h381, h429, h433, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h429, h430, hc35, hlam, hphi, u3ehi3]
                · linarith only [h379, h381, h429, hlam]
              · linarith only [h426, h428, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h426, h427, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h446 | h446
            · rcases m.htr 0 2 5 (by decide) (by decide) with h447 | h447
              · rcases m.htr 0 3 4 (by decide) (by decide) with h448 | h448
                · rcases m.htr 0 3 5 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h450 | h450
                    · linarith only [h381, h382, h450, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
                      · linarith only [h426, h452, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h452, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h448, h449, hc35, hlam, hphi, u3ehi3]
                · linarith only [h379, h381, h448, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h457 | h457
                · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                    · linarith only [h0, h381, h447, h459, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
                      · linarith only [h0, h426, h461, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h381, h457, h461, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h457, h458, hc35, hlam, hphi, u3ehi3]
                · linarith only [h379, h381, h457, hlam]
            · linarith only [h0, h381, h446, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h467 | h467
        · rcases m.htr 0 2 3 (by decide) (by decide) with h468 | h468
          · rcases m.htr 0 2 4 (by decide) (by decide) with h469 | h469
            · rcases m.htr 0 2 5 (by decide) (by decide) with h470 | h470
              · rcases m.htr 0 3 4 (by decide) (by decide) with h471 | h471
                · rcases m.htr 0 3 5 (by decide) (by decide) with h472 | h472
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h473 | h473
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h475 | h475
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h476 | h476
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h477 | h477
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h478 | h478
                              · linarith only [h381, h467, h474, h477, h478, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                              · linarith only [h379, h471, h478, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h379, h471, h477, hlam]
                          · linarith only [h0, h468, h471, h476, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                        · linarith only [h0, h467, h472, h475, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
                      · linarith only [h0, h467, h472, h474, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · linarith only [h381, h467, h473, hlam]
                  · linarith only [h471, h472, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h471, h487, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h379, h467, h487, hlam]
              · linarith only [h468, h470, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h468, h469, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h492 | h492
            · rcases m.htr 0 2 5 (by decide) (by decide) with h493 | h493
              · rcases m.htr 0 3 4 (by decide) (by decide) with h494 | h494
                · rcases m.htr 0 3 5 (by decide) (by decide) with h495 | h495
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h496 | h496
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
                      · linarith only [h468, h497, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h467, h495, h497, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · linarith only [h381, h467, h496, hlam]
                  · linarith only [h494, h495, hc35, hlam, hphi, u3ehi3]
                · linarith only [h468, h492, h494, hlam]
              · linarith only [h0, h467, h493, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h504 | h504
              · rcases m.htr 0 3 4 (by decide) (by decide) with h505 | h505
                · rcases m.htr 0 3 5 (by decide) (by decide) with h506 | h506
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h507 | h507
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
                      · linarith only [h0, h468, h508, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h467, h506, h508, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · linarith only [h0, h467, h492, h507, hlam]
                  · linarith only [h505, h506, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h513 | h513
                  · linarith only [h505, h513, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h379, h467, h513, hlam]
              · linarith only [h0, h467, h504, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h517 | h517
          · rcases m.htr 0 2 4 (by decide) (by decide) with h518 | h518
            · rcases m.htr 0 2 5 (by decide) (by decide) with h519 | h519
              · rcases m.htr 0 3 4 (by decide) (by decide) with h520 | h520
                · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h525 | h525
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                                  · linarith only [h517, h529, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                  · linarith only [h520, h529, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                                · linarith only [h381, h522, h528, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h379, h520, h521, h527, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi3]
                            · linarith only [h379, h520, h526, hlam]
                          · linarith only [h0, h519, h525, hlam]
                        · linarith only [h0, h518, h524, hlam]
                      · linarith only [h0, h517, h523, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                                · linarith only [h381, h522, h539, h543, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                                  · linarith only [h517, h545, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                  · linarith only [h520, h545, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                              · linarith only [h379, h521, h542, hlam]
                            · linarith only [h379, h520, h541, hlam]
                          · linarith only [h0, h519, h540, hlam]
                        · linarith only [h0, h517, h520, h539, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                      · linarith only [h0, h517, h520, h538, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h520, h521, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h554 | h554
                  · linarith only [h520, h554, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h559 | h559
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                            · linarith only [h520, h557, h560, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h562 | h562
                              · linarith only [h517, h554, h560, h562, hc34, hlam, hphi, u3ehi2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                                  · linarith only [h379, h517, h560, h565, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h567 | h567
                                    · linarith only [h0, h379, h518, h562, h565, h567, hc01, hlam, hphi, ht12, u2elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h569 | h569
                                      · rcases h0bigk with h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [hlam, p570_0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h379, hlam, p570_0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h381, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h467, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p570_1, u2elo1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [hlam, p570_0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p570_1, u2elo1, u3ehi0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h556, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p570_1, u2elo1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h467, hc01, hlam, hphi, ht12, p570_1, u2elo1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h379, h562, h569, hc01, hc34, hlam, hphi, ht12, ht23, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h517, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [hlam, p570_0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h520, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h554, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h518, hc01, hlam, hphi, ht12, p570_1, u2elo1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h518, hlam, p570_0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h518, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p570_1, u2elo1, u3ehi0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [hlam, p570_0]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h517, h518, h554, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p570_1, u2elo1, u3ehi2]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h519, hc01, hlam, hphi, ht12, p570_1, u2elo1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h519, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h0, h517, h519, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p570_1, u2elo1, u3ehi2]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [h556, hlam, p570_1]
                                        · have p570_0 := h570c.1
                                          have p570_1 := h570c.2.1
                                          have p570_2 := h570c.2.2.1
                                          have p570_3 := h570c.2.2.2
                                          linarith only [hlam, p570_0]
                                      · linarith only [h517, h520, h569, hc45, hlam, hphi, ht34, u3ehi2]
                                · linarith only [h381, h556, h564, hlam]
                          · linarith only [h0, h519, h559, hlam]
                        · linarith only [h0, h518, h558, hlam]
                      · linarith only [h0, h557, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
                            · linarith only [h517, h520, h601, h604, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h606 | h606
                              · linarith only [h604, h606, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h608 | h608
                                · linarith only [h517, h520, h556, h602, h608, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h610 | h610
                                  · linarith only [h517, h610, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
                                    · linarith only [h518, h606, h610, h612, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                                      · linarith only [h0, h381, h518, h608, h610, h614, hc01, hc34, hlam, hphi, ht12, u2elo1, u3ehi2]
                                      · linarith only [h520, h614, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h0, h519, h603, hlam]
                        · linarith only [h0, h518, h602, hlam]
                      · linarith only [h0, h601, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h517, h519, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h517, h518, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h622 | h622
            · rcases m.htr 0 2 5 (by decide) (by decide) with h623 | h623
              · rcases m.htr 0 3 4 (by decide) (by decide) with h624 | h624
                · rcases m.htr 0 3 5 (by decide) (by decide) with h625 | h625
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h626 | h626
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h627 | h627
                      · linarith only [h517, h627, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h627, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                      · linarith only [h517, h630, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h630, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h624, h625, hc35, hlam, hphi, u3ehi3]
                · linarith only [h517, h622, h624, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h635 | h635
                · rcases m.htr 0 3 5 (by decide) (by decide) with h636 | h636
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h637 | h637
                    · linarith only [h622, h623, h637, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
                      · linarith only [h517, h639, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h639, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h635, h636, hc35, hlam, hphi, u3ehi3]
                · linarith only [h517, h622, h635, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h644 | h644
              · rcases m.htr 0 3 4 (by decide) (by decide) with h645 | h645
                · rcases m.htr 0 3 5 (by decide) (by decide) with h646 | h646
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h647 | h647
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
                      · linarith only [h517, h648, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h648, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h622, h644, h647, hlam]
                  · linarith only [h645, h646, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h653 | h653
                  · linarith only [h645, h653, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h517, h644, h653, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h656 | h656
                · rcases m.htr 0 3 5 (by decide) (by decide) with h657 | h657
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                      · linarith only [h517, h659, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h659, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
                      · linarith only [h0, h517, h662, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h662, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h656, h657, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h666 | h666
                  · linarith only [h656, h666, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h669 | h669
                      · linarith only [h0, h517, h669, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h669, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                      · linarith only [h0, h517, h672, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h672, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_M_LR_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h4, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h11, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h16, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h21, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h21, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · linarith only [h19, h20, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h26, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h26, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h29, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                  · linarith only [h35, h4, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
                    · linarith only [h1, h35, h37, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h39 | h39
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                        · linarith only [h1, h40, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h33, h37, h39, h40, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                      · linarith only [h1, h32, h35, h39, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                  · linarith only [h4, h44, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h46, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h1, h49, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h1, h33, h46, h48, h49, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                      · linarith only [h1, h32, h44, h48, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                · linarith only [h32, h33, h53, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                  · linarith only [h4, h55, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h57, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
                        · linarith only [h1, h33, h60, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h3, h53, h59, h60, h62, hlam, hphi, u0ehi8, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                              · linarith only [h32, h33, h65, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                              · linarith only [h3, h4, h57, h59, h60, h65, hc35, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                            · linarith only [h3, h4, h59, h60, h64, hlam, hphi, u0ehi6, u0elo0]
                      · linarith only [h32, h33, h59, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                  · linarith only [h4, h72, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                    · linarith only [h1, h72, h74, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                      · linarith only [h1, h32, h76, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h2, h76, h78, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h70, h72, h78, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                · linarith only [h32, h70, h71, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                  · linarith only [h4, h83, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
                    · linarith only [h1, h83, h85, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                      · linarith only [h1, h32, h4, h87, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                        · linarith only [h2, h4, h70, h87, h89, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                          · linarith only [h2, h91, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h2, h82, h83, h87, h91, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                  · linarith only [h4, h94, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                    · linarith only [h1, h32, h4, h82, h94, h96, hc45, hlam, hphi, ht23, ht34, u0ehi6, u0elo0, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                      · linarith only [h1, h32, h4, h98, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                        · linarith only [h100, h2, h4, h70, h98, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h102, h2, h32, h4, h82, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                            · linarith only [h104, h32, h4, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                            · linarith only [h102, h104, h3, h4, h94, h98, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h107 | h107
          · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
              · linarith only [h1, h109, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                · linarith only [h0, h107, h108, h109, h111, h3, hc35, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                  · linarith only [h0, h113, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h107, h113, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
              · linarith only [h0, h107, h108, h116, h3, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
                · linarith only [h118, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h120, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi2]
                  · linarith only [h107, h120, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
            · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h1, h124, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                · linarith only [h126, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h128, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                    · linarith only [h1, h128, h130, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                        · linarith only [h1, h107, h124, h133, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1, h130, h132, h133, h3, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h123, h124, h132, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
              · linarith only [h0, h123, h137, h3, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                · linarith only [h139, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                  · linarith only [h0, h107, h141, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h1, h141, h143, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                      · linarith only [h1, h107, h123, h145, h3, hlam, hphi, u0ehi6, u0elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                        · linarith only [h107, h137, h145, h147, h2, h3, hlam, hphi, u0ehi6, u0elo4]
                        · linarith only [h141, h145, h147, h2, h3, hc35, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h150 | h150
        · rcases m.htr 0 2 3 (by decide) (by decide) with h151 | h151
          · rcases m.htr 0 3 4 (by decide) (by decide) with h152 | h152
            · linarith only [h1, h152, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                  · linarith only [h0, h156, h2, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h151, h156, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h151, h155, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
                · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                  · linarith only [h0, h161, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h151, h161, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h151, h160, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h165 | h165
            · linarith only [h1, h165, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                  · linarith only [h0, h151, h169, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                    · linarith only [h0, h171, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h1, h169, h171, h2, hc24, hlam, hphi, u2ehi1]
                · linarith only [h0, h168, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                  · linarith only [h0, h151, h176, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                    · linarith only [h1, h176, h178, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h1, h176, h178, h2, hc24, hlam, hphi, u2ehi1]
                · linarith only [h0, h175, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h182 | h182
          · rcases m.htr 0 3 4 (by decide) (by decide) with h183 | h183
            · linarith only [h1, h183, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
              · linarith only [h0, h150, h182, h183, h185, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h187 | h187
                · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                  · linarith only [h0, h188, h2, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h182, h188, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                · linarith only [h0, h182, h187, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
            · linarith only [h1, h192, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h194 | h194
              · linarith only [h0, h150, h192, h194, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
                  · linarith only [h0, h197, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                    · linarith only [h0, h150, h196, h199, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h1, h197, h199, h2, hc24, hlam, hphi, u2ehi1]
                · linarith only [h0, h196, h2, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h203 | h203
      · rcases m.htr 0 1 5 (by decide) (by decide) with h204 | h204
        · rcases m.htr 0 2 3 (by decide) (by decide) with h205 | h205
          · linarith only [h0, h1, h205, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h207 | h207
            · rcases m.htr 0 3 5 (by decide) (by decide) with h208 | h208
              · rcases m.htr 0 4 5 (by decide) (by decide) with h209 | h209
                · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                  · linarith only [h205, h210, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h210, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                  · linarith only [h0, h213, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h1, h213, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h208, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h207, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h218 | h218
          · linarith only [h0, h1, h218, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h220 | h220
            · rcases m.htr 0 3 5 (by decide) (by decide) with h221 | h221
              · rcases m.htr 0 4 5 (by decide) (by decide) with h222 | h222
                · linarith only [h203, h204, h222, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                  · linarith only [h0, h218, h224, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · linarith only [h0, h1, h224, hc23, hlam, hphi, u2ehi1]
              · linarith only [h0, h1, h221, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h220, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
        · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
          · linarith only [h0, h1, h230, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h232 | h232
            · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
                · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                  · linarith only [h0, h230, h235, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
                  · linarith only [h0, h1, h235, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h203, h234, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h0, h203, h232, h233, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h232, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h241 | h241
          · linarith only [h0, h1, h241, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
            · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
              · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
                · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
                  · linarith only [h241, h246, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h246, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h203, h245, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h0, h203, h243, h244, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h1, h243, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h252 | h252
    · rcases m.htr 0 1 4 (by decide) (by decide) with h253 | h253
      · rcases m.htr 0 1 5 (by decide) (by decide) with h254 | h254
        · rcases m.htr 0 2 3 (by decide) (by decide) with h255 | h255
          · rcases m.htr 0 3 4 (by decide) (by decide) with h256 | h256
            · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
              · rcases m.htr 0 4 5 (by decide) (by decide) with h258 | h258
                · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h252, h262, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h257, h260, h261, h262, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                      · linarith only [h0, h252, h256, h259, h261, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h0, h252, h257, h260, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h252, h255, h256, h258, h259, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                        · linarith only [h252, h271, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                        · linarith only [h257, h270, h271, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h252, h256, h268, h270, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h252, h257, h269, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h252, h257, h258, h268, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h277 | h277
                · linarith only [h256, h257, h277, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h252, h257, h282, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
                          · linarith only [h277, h284, hc14, hlam, hphi, ht01, u0ehi8]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h287 | h287
                              · linarith only [h0, h254, h256, h257, h279, h282, h287, hc12, hlam, hphi, ht01, u0ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h289 | h289
                                · linarith only [h277, h289, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h291 | h291
                                  · linarith only [h277, h291, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                  · rcases h3bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h257, h280, h281, h291, hc45, hlam, hphi, ht23, ht34, p293_1, u2ehi3]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h257, h291, hc23, hc45, hlam, hphi, ht34, p293_1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h257, h291, hc34, hc45, hlam, hphi, p293_1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h257, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h252, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h0, h252, h256, h257, h291, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p293_1, u0ehi8, u2ehi2]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h0, h252, h256, h257, h291, hc12, hc34, hc45, hlam, hphi, ht01, p293_1, u0ehi8]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h282, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h255, hlam, p293_1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h279, hlam, p293_1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h255, h256, h257, h291, hc34, hc45, hlam, hphi, p293_1, u0ehi8, u0elo1]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h287, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h256, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h281, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h286, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h291, hlam, p293_0]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h256, h291, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p293_1, u0ehi8]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h280, h281, h291, hc45, hlam, hphi, ht23, ht34, p293_1, u2ehi3]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [h286, h291, hc45, hlam, hphi, ht23, ht34, p293_1, u2ehi3]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      rcases p293_3 (m.d 0 3) (by simp) with h317 | h317
                                      · linarith only [h257, h317, hlam]
                                      · linarith only [h256, h317, hlam]
                                    · have p293_0 := h293c.1
                                      have p293_1 := h293c.2.1
                                      have p293_2 := h293c.2.2.1
                                      have p293_3 := h293c.2.2.2
                                      linarith only [hlam, p293_0]
                            · linarith only [h256, h286, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                      · linarith only [h256, h257, h279, h281, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h254, h280, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h254, h279, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h325 | h325
              · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
                · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                      · linarith only [h252, h256, h325, h329, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
                        · linarith only [h0, h253, h329, h331, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h256, h325, h331, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h328, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h253, h256, h325, h327, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h256, h325, h326, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h337 | h337
                · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                      · linarith only [h252, h256, h340, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
                        · linarith only [h0, h253, h325, h340, h342, hc12, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h344 | h344
                          · linarith only [h0, h253, h344, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h337, h339, h344, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                    · linarith only [h0, h253, h337, h339, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h253, h337, h338, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                      · linarith only [h252, h256, h351, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                        · linarith only [h325, h353, hc13, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                          · linarith only [h0, h253, h256, h337, h355, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                            · linarith only [h256, h357, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                              · linarith only [h0, h254, h325, h349, h351, h355, h359, hc12, hlam, hphi, ht01, u0ehi7]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h361 | h361
                                · linarith only [h0, h254, h256, h337, h349, h351, h355, h361, hc12, hc24, hlam, hphi, ht01, u0ehi7, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                                  · linarith only [h0, h254, h256, h337, h349, h351, h355, h363, hc12, hc34, hlam, hphi, ht01, ht23, u0ehi7, u2ehi2]
                                  · linarith only [h0, h254, h256, h349, h351, h355, h363, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u2ehi2]
                    · linarith only [h0, h254, h350, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h254, h349, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h252, h255, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h369 | h369
          · rcases m.htr 0 3 4 (by decide) (by decide) with h370 | h370
            · rcases m.htr 0 3 5 (by decide) (by decide) with h371 | h371
              · linarith only [h252, h254, h371, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h373 | h373
                · linarith only [h252, h254, h370, h373, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                        · linarith only [h252, h254, h370, h371, h378, hlam, hphi, u0ehi8, u0elo4]
                        · linarith only [h252, h254, h376, h377, h378, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h370, h371, h377, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h376, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h252, h369, h370, h375, hlam, hphi, u0ehi8, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
              · linarith only [h252, h254, h384, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h386 | h386
                · linarith only [h253, h254, h386, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h390 | h390
                      · linarith only [h252, h370, h390, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h392 | h392
                        · linarith only [h384, h392, hc13, hlam, hphi, ht01, u0ehi7]
                        · linarith only [h253, h254, h388, h390, h392, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h252, h388, h389, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h388, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h252, h369, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h398 | h398
        · rcases m.htr 0 2 3 (by decide) (by decide) with h399 | h399
          · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
            · linarith only [h252, h253, h400, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h402 | h402
              · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
                · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                      · linarith only [h252, h400, h406, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h252, h253, h404, h406, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h252, h404, h405, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h398, h404, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h253, h398, h403, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h412 | h412
                · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h415 | h415
                      · linarith only [h252, h400, h415, hlam, hphi, u0ehi7, u0elo0]
                      · linarith only [h252, h253, h413, h415, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h252, h413, h414, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h413, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h253, h398, h412, hlam]
          · linarith only [h0, h252, h399, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h422 | h422
          · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
            · linarith only [h252, h253, h423, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
              · linarith only [h252, h398, h425, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                      · linarith only [h252, h423, h430, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h252, h253, h428, h430, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h252, h428, h429, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h428, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h435 | h435
                  · linarith only [h252, h253, h427, h435, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h252, h435, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · linarith only [h0, h252, h422, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h439 | h439
      · rcases m.htr 0 1 5 (by decide) (by decide) with h440 | h440
        · rcases m.htr 0 2 3 (by decide) (by decide) with h441 | h441
          · rcases m.htr 0 3 4 (by decide) (by decide) with h442 | h442
            · rcases m.htr 0 3 5 (by decide) (by decide) with h443 | h443
              · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
                · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                          · linarith only [h439, h449, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h252, h439, h441, h444, h446, h449, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                        · linarith only [h252, h440, h448, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h252, h441, h442, h447, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h252, h439, h444, h445, h446, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h439, h444, h445, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h459 | h459
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h460 | h460
                          · linarith only [h439, h444, h460, hlam, hphi, u0ehi8, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h462 | h462
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h463 | h463
                              · linarith only [h441, h463, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h441, h443, h462, h463, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h441, h442, h462, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h252, h440, h459, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h252, h439, h457, h458, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h252, h456, h457, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h441, h456, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h252, h440, h443, hlam]
            · linarith only [h252, h439, h442, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h473 | h473
            · rcases m.htr 0 3 5 (by decide) (by decide) with h474 | h474
              · rcases m.htr 0 4 5 (by decide) (by decide) with h475 | h475
                · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                  · linarith only [h441, h476, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h439, h475, h476, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h479 | h479
                  · linarith only [h0, h440, h441, h475, h479, hc12, hlam, hphi, ht01, u0ehi8]
                  · linarith only [h0, h440, h475, h479, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · linarith only [h0, h440, h441, h474, hlam]
            · linarith only [h0, h439, h441, h473, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h484 | h484
          · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
            · rcases m.htr 0 3 5 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
                · linarith only [h439, h440, h487, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h492 | h492
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h493 | h493
                          · linarith only [h439, h440, h484, h486, h487, h493, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h439, h440, h490, h493, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · linarith only [h252, h439, h484, h486, h490, h492, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                      · linarith only [h252, h439, h490, h491, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h252, h489, h490, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h439, h484, h489, hlam, hphi, u0ehi8, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h500 | h500
                · linarith only [h439, h440, h500, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h503 | h503
                    · linarith only [h252, h439, h486, h503, hc35, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h252, h502, h503, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h439, h484, h502, hlam, hphi, u0ehi8, u0elo1]
            · linarith only [h252, h439, h485, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h508 | h508
            · rcases m.htr 0 3 5 (by decide) (by decide) with h509 | h509
              · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
                · linarith only [h439, h440, h510, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                  · linarith only [h0, h484, h512, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h439, h512, hc23, hlam, hphi, ht01, ht12, u0ehi8]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h515 | h515
                · linarith only [h0, h439, h484, h509, h515, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
                  · linarith only [h0, h484, h517, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h439, h517, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h439, h484, h508, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h521 | h521
        · rcases m.htr 0 2 3 (by decide) (by decide) with h522 | h522
          · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
            · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
              · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
                · rcases m.htr 1 2 3 (by decide) (by decide) with h526 | h526
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h527 | h527
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h528 | h528
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h532 | h532
                              · linarith only [h522, h532, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h521, h529, h531, h532, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h522, h523, h531, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                          · linarith only [h439, h521, h530, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                        · linarith only [h439, h521, h528, h529, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h252, h521, h522, h523, h528, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                    · linarith only [h252, h521, h526, h527, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h521, h526, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h439, h521, h525, hlam]
              · linarith only [h252, h521, h524, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h543 | h543
              · rcases m.htr 0 4 5 (by decide) (by decide) with h544 | h544
                · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h547 | h547
                      · linarith only [h523, h543, h545, h547, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h252, h521, h547, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h0, h521, h546, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h521, h522, h545, hlam, hphi, u0ehi9, u0elo1]
                · linarith only [h252, h521, h523, h544, hlam]
              · linarith only [h252, h521, h543, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
            · rcases m.htr 0 3 5 (by decide) (by decide) with h555 | h555
              · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
                · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
                  · linarith only [h522, h557, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h521, h557, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h439, h521, h556, hlam]
              · linarith only [h0, h521, h522, h555, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h562 | h562
              · rcases m.htr 0 4 5 (by decide) (by decide) with h563 | h563
                · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                  · linarith only [h0, h521, h522, h564, hc12, hlam, hphi, ht01, u0ehi9]
                  · linarith only [h0, h521, h564, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h521, h522, h554, h563, hlam]
              · linarith only [h0, h521, h522, h562, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h569 | h569
          · rcases m.htr 0 3 4 (by decide) (by decide) with h570 | h570
            · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
              · rcases m.htr 0 4 5 (by decide) (by decide) with h572 | h572
                · rcases m.htr 1 2 3 (by decide) (by decide) with h573 | h573
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h574 | h574
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                              · linarith only [h569, h579, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                              · linarith only [h571, h578, h579, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h569, h570, h578, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                          · linarith only [h439, h572, h577, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h439, h569, h571, h575, h576, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h252, h569, h570, h575, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h252, h573, h574, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h573, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h592 | h592
                          · linarith only [h439, h572, h588, h590, h592, hc12, hlam, hphi, ht01, u0ehi5]
                          · linarith only [h439, h592, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                        · linarith only [h252, h569, h571, h591, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h252, h569, h570, h590, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h0, h589, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h569, h588, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h599 | h599
                · linarith only [h570, h571, h599, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h604 | h604
                        · linarith only [h571, h601, h604, hc12, hlam, hphi, ht01, u0ehi7]
                        · linarith only [h252, h604, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h252, h570, h603, hlam, hphi, u0ehi5, u0elo2]
                    · linarith only [h0, h602, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h569, h601, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h610 | h610
              · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
                · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h613 | h613
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h614 | h614
                      · linarith only [h570, h610, h612, h614, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h252, h614, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h613, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h569, h612, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h570, h610, h611, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h623 | h623
                      · linarith only [h570, h621, h623, hc12, hlam, hphi, ht01, u0ehi7]
                      · linarith only [h252, h623, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h622, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h569, h621, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h630 | h630
                      · linarith only [h252, h570, h628, h630, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h252, h630, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h629, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h569, h628, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h635 | h635
            · rcases m.htr 0 3 5 (by decide) (by decide) with h636 | h636
              · rcases m.htr 0 4 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 1 2 3 (by decide) (by decide) with h638 | h638
                  · linarith only [h0, h569, h638, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h638, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
                  · linarith only [h0, h569, h641, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h641, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h644 | h644
                · linarith only [h635, h636, h644, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                  · linarith only [h0, h569, h646, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h646, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h649 | h649
              · rcases m.htr 0 4 5 (by decide) (by decide) with h650 | h650
                · rcases m.htr 1 2 3 (by decide) (by decide) with h651 | h651
                  · linarith only [h0, h569, h651, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h651, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h635, h649, h650, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
                · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
                  · linarith only [h0, h569, h656, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h656, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                  · linarith only [h0, h569, h659, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h659, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_21_14_M_LI_L_R_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h2, h4, h5, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h2, h9, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
              · rcases h1bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u1elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  rcases p11_3 (m.d 0 1) (by simp) with h14 | h14
                  · rcases p11_3 (m.d 1 2) (by simp) with h15 | h15
                    · linarith only [h0, h15, hlam]
                    · linarith only [h15, h4, hlam]
                  · linarith only [h14, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p11_1, u1elo0, u4ehi1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h4, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u1elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h5, h9, hc13, hc45, hlam, hphi, ht34, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h5, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h5, h9, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h1, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h4, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h7, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h9, hlam, hphi, ht01, ht0b, ht45, ht5b, p11_1, u1elo2, u4ehi1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h2, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u1elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h9, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h3, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u1elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u1elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h3, hlam, hphi, ht01, ht0b, ht45, ht5b, p11_1, u1elo0, u4ehi1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
          · linarith only [h0, h41, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
            · linarith only [h1, h43, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h45 | h45
              · linarith only [h2, h45, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
              · rcases h1bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  rcases p47_3 (m.d 0 1) (by simp) with h49 | h49
                  · rcases p47_3 (m.d 1 2) (by simp) with h50 | h50
                    · linarith only [h50, hlam, p47_0]
                    · rcases p47_3 (m.d 1 3) (by simp) with h52 | h52
                      · linarith only [h1, h52, hlam]
                      · linarith only [h4, h52, hlam]
                  · linarith only [h49, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  rcases p47_3 (m.d 0 1) (by simp) with h56 | h56
                  · rcases p47_3 (m.d 1 2) (by simp) with h57 | h57
                    · linarith only [h0, h57, hlam]
                    · rcases p47_3 (m.d 1 3) (by simp) with h59 | h59
                      · linarith only [h59, hlam, p47_0]
                      · rcases p47_3 (m.d 1 4) (by simp) with h61 | h61
                        · linarith only [h2, h61, hlam]
                        · linarith only [h43, h61, hlam]
                  · linarith only [h56, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p47_1, u1elo0, u4ehi1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h45, hlam, hphi, ht01, ht0b, ht45, ht5b, p47_1, u1elo0, u4ehi1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h0, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h4, hlam, p47_1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h41, hlam, p47_1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h45, hlam, hphi, ht01, ht0b, ht45, ht5b, p47_1, u1elo1, u4ehi1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h1, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p47_1, u1elo0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h43, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h43, h45, hlam, p47_1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h2, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h45, hc12, hc45, hlam, hphi, ht23, ht34, p47_1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h3, h45, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p47_1, u1elo0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h45, hlam, p47_1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h3, hlam, p47_0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p47_1, u1elo0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p47_1, u1elo0]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [h3, hlam, hphi, ht01, ht0b, ht45, ht5b, p47_1, u1elo0, u4ehi1]
                · have p47_0 := h47c.1
                  have p47_1 := h47c.2.1
                  have p47_2 := h47c.2.2.1
                  have p47_3 := h47c.2.2.2
                  linarith only [hlam, p47_0]
      · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h88 | h88
      · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
        · linarith only [h0, h2, h89, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
          · linarith only [h1, h2, h89, h91, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
            · linarith only [h1, h2, h93, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
              · linarith only [h2, h88, h95, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
              · linarith only [h1, h2, h89, h95, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
        · linarith only [h0, h2, h98, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
          · linarith only [h1, h100, h2, h98, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
            · linarith only [h1, h102, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
              · rcases h1bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h104, h88, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u1elo3]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h104, h88, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p105_1, u1elo3]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h2, hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h88, hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h0, hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h98, hlam, p105_1]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h100, hlam, p105_1]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h88, hc01, hlam, hphi, p105_1, u1elo1]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h1, hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h1, h88, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u1elo4]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h102, hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h1, h88, hlam, p105_1]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [hc01, hlam, hphi, p105_1, u1elo3]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  rcases p105_3 (m.d 0 1) (by simp) with h122 | h122
                  · linarith only [h122, h2, hlam]
                  · linarith only [h0, h122, hlam]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  rcases p105_3 (m.d 0 1) (by simp) with h125 | h125
                  · linarith only [h125, h2, hlam]
                  · linarith only [h1, h125, hlam]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h1, h88, h98, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u1elo3]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h1, h98, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u1elo4]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  rcases p105_3 (m.d 0 1) (by simp) with h131 | h131
                  · linarith only [h131, h88, hlam]
                  · linarith only [h0, h131, hlam]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  rcases p105_3 (m.d 0 1) (by simp) with h134 | h134
                  · linarith only [h134, h88, hlam]
                  · linarith only [h1, h134, hlam]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [h104, hlam, p105_0]
                · have p105_0 := h105c.1
                  have p105_1 := h105c.2.1
                  have p105_2 := h105c.2.2.1
                  have p105_3 := h105c.2.2.2
                  linarith only [hlam, p105_0]
              · linarith only [h1, h104, h2, h98, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
    · linarith only [h1, h140, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h142 | h142
      · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
        · linarith only [h0, h1, h143, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
          · linarith only [h0, h1, h145, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
            · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
              · linarith only [h140, h142, h147, h148, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
              · linarith only [h0, h140, h148, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h0, h1, h147, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
        · linarith only [h0, h1, h152, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
          · linarith only [h0, h1, h154, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
            · rcases m.htr 1 4 5 (by decide) (by decide) with h157 | h157
              · rcases h1bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h142, h156, h157, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo2]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h1, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h140, hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h142, hlam, p158_0]
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
                  linarith only [h152, hlam, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h154, hlam, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h142, hc01, hlam, hphi, p158_1, u1elo1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo2]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  rcases p158_3 (m.d 0 1) (by simp) with h170 | h170
                  · linarith only [h1, h170, hlam]
                  · linarith only [h0, h170, hlam]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1, u1elo2, u4ehi1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h142, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo2]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo3]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  rcases p158_3 (m.d 0 1) (by simp) with h177 | h177
                  · linarith only [h140, h177, hlam]
                  · linarith only [h0, h177, hlam]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h156, hlam, p158_1]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [hlam, p158_0]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, h142, h156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo2]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p158_1, u1elo4]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  rcases p158_3 (m.d 0 1) (by simp) with h184 | h184
                  · linarith only [h142, h184, hlam]
                  · linarith only [h0, h184, hlam]
                · have p158_0 := h158c.1
                  have p158_1 := h158c.2.1
                  have p158_2 := h158c.2.2.1
                  have p158_3 := h158c.2.2.2
                  linarith only [h156, h157, hlam, p158_1]
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
              · linarith only [h0, h140, h157, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h0, h1, h156, hc12, hc34, hlam, hphi, ht23]

end R2N4
