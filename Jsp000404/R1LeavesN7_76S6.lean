import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
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
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · linarith only [h13, h7, hc23, hlam, hphi, u3elo0]
                          · linarith only [h12, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h20, h24, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · linarith only [h22, h24, hc23, hlam, hphi, u3elo1]
                          · linarith only [h23, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h22, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h21, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h20, h3, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h31, h6, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h35, h7, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                            · linarith only [h33, h38, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                            · rcases h0bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h34, h37, h38, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h1, h33, h37, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                rcases p40_3 (m.d 0 1) (by simp) with h44 | h44
                                · rcases p40_3 (m.d 0 2) (by simp) with h45 | h45
                                  · linarith only [h0, h45, hlam]
                                  · linarith only [h4, h45, hlam]
                                · linarith only [h44, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h1, h33, h37, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
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
                                linarith only [h1, h33, h37, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p40_1, u2elo0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h1, h33, h37, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p40_1, u2elo0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h1, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h3, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h4, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p40_1, u3elo4]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h7, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h34, h37, h38, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h4, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h6, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h31, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h5, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h31, hc03, hc45, hlam, hphi, ht34, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p40_1, u3elo4]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                          · linarith only [h37, h6, hc23, hlam, hphi, u3elo0]
                      · linarith only [h34, h5, hc12, hlam, hphi, u2elo0]
                    · linarith only [h3, h33, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h73 | h73
                · linarith only [h6, h73, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h73, h78, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                          · linarith only [h3, h6, h75, h80, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                            · linarith only [h1, h73, h76, h82, hlam]
                            · rcases h0bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h0, h77, h82, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                rcases p84_3 (m.d 0 1) (by simp) with h87 | h87
                                · rcases p84_3 (m.d 0 2) (by simp) with h88 | h88
                                  · linarith only [h0, h88, hlam]
                                  · linarith only [h3, h88, hlam]
                                · linarith only [h1, h87, hlam]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h75, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi4]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h2, h77, hc01, hlam, hphi, ht0b, ht5b, p84_1, u5ehi2]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h0, hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h75, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0, u5ehi4]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h2, h77, hlam, hphi, ht01, ht0b, ht12, ht5b, p84_1, u2elo0, u5ehi2]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h1, hlam, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h3, hlam, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h6, hlam, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h73, hlam, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h0, h77, hc04, hlam, hphi, ht0b, ht5b, p84_1, u5ehi2]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h4, hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h1, h6, h76, hc23, hlam, hphi, p84_1, u3elo3]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h2, h6, h77, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p84_1, u3elo3, u5ehi2]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h2, hlam, p84_0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h5, hlam, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h1, h5, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo0]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [h75, hlam, p84_1]
                              · have p84_0 := h84c.1
                                have p84_1 := h84c.2.1
                                have p84_2 := h84c.2.2.1
                                have p84_3 := h84c.2.2.2
                                linarith only [hlam, p84_0]
                      · linarith only [h5, h77, hc12, hlam, hphi, u2elo0]
                    · linarith only [h3, h76, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h1, h118, h2, h6, h73, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                          · linarith only [h120, h3, h6, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                            · linarith only [h116, h122, h73, hc03, hlam, hphi, u3elo1]
                            · rcases h0bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, h117, hc01, hlam, hphi, ht0b, ht5b, p124_1, u5ehi2]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h127 | h127
                                · rcases p124_3 (m.d 0 2) (by simp) with h128 | h128
                                  · linarith only [h0, h128, hlam]
                                  · linarith only [h128, h3, hlam]
                                · linarith only [h1, h127, hlam]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h132 | h132
                                · rcases p124_3 (m.d 0 2) (by simp) with h133 | h133
                                  · linarith only [h0, h133, hlam]
                                  · linarith only [h133, h4, hlam]
                                · linarith only [h132, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p124_1, u5ehi0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h1, h116, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h1, h116, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht5b, p124_1, u2elo0, u5ehi1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h1, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h3, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h6, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h73, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, h117, hc04, hlam, hphi, ht0b, ht5b, p124_1, u5ehi2]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h4, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h1, h116, h6, hc23, hlam, hphi, p124_1, u3elo3]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h75, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h2, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h5, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h1, h116, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h73, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p124_1, u3elo4]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                      · linarith only [h116, h117, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h116, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h160 | h160
              · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
                · linarith only [h161, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h163 | h163
                  · linarith only [h160, h163, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h166, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                        · linarith only [h1, h161, h168, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                          · linarith only [h0, h165, h170, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · linarith only [h160, h161, h170, hc23, hlam, hphi, u3elo4]
                    · linarith only [h165, h3, h5, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
                · linarith only [h160, h174, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h176, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
                      · linarith only [h179, h5, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                        · linarith only [h1, h174, h181, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                          · linarith only [h160, h178, h179, h183, h2, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                            · linarith only [h0, h174, h178, h185, h5, hlam]
                            · linarith only [h0, h178, h185, h5, hc23, hlam, hphi, u3elo4]
                    · linarith only [h178, h3, h5, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h189 | h189
            · linarith only [h189, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h191 | h191
              · linarith only [h191, h3, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                · linarith only [h193, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h197 | h197
                      · linarith only [h189, h197, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h1, h193, h199, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                          · linarith only [h0, h189, h191, h196, h201, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · linarith only [h201, h3, h4, hc23, hlam, hphi, u3elo3]
                    · linarith only [h196, h3, h4, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                      · linarith only [h0, h206, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                        · linarith only [h1, h208, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                          · linarith only [h0, h191, h205, h210, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · linarith only [h210, h3, h4, hc23, hlam, hphi, u3elo3]
                    · linarith only [h205, h3, h4, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
          · rcases m.htr 0 2 5 (by decide) (by decide) with h215 | h215
            · linarith only [h215, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
                · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h214, h219, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                    · linarith only [h221, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h0, h223, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                            · rcases h0bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h214, h226, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p228_1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h218, hc01, hlam, hphi, ht0b, ht5b, p228_1, u5ehi0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                rcases p228_3 (m.d 0 1) (by simp) with h232 | h232
                                · rcases p228_3 (m.d 0 2) (by simp) with h233 | h233
                                  · linarith only [h0, h233, hlam]
                                  · linarith only [h214, h233, hlam]
                                · linarith only [h232, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p228_1, u5ehi0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h0, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h3, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h215, h227, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p228_1, u3elo2]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h215, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h1, hlam, p228_1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, ht23, p228_1, u3elo2]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h214, h226, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p228_1, u3elo2]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h214, h215, h226, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p228_1, u3elo2]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h214, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h217, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h219, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h2, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h214, h226, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p228_1]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h218, hlam, p228_0]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [h215, h227, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p228_1, u3elo2]
                              · have p228_0 := h228c.1
                                have p228_1 := h228c.2.1
                                have p228_2 := h228c.2.2.1
                                have p228_3 := h228c.2.2.2
                                linarith only [hlam, p228_0]
                            · linarith only [h227, h3, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h1, h225, h226, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h218, h225, h3, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
                  · linarith only [h214, h218, h261, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
                    · linarith only [h0, h218, h263, h3, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                      · linarith only [h0, h218, h265, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                        · linarith only [h1, h217, h218, h267, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                            · linarith only [h218, h270, hc03, hlam, hphi, u3elo2]
                            · linarith only [h214, h269, h270, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h269, h3, hc02, hlam, hphi, ht23, u3elo3]
              · linarith only [h214, h217, h3, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
            · linarith only [h275, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h277 | h277
              · rcases m.htr 0 3 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 0 4 5 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
                    · linarith only [h280, h3, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h282 | h282
                      · linarith only [h0, h2, h275, h282, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                            · rcases h0bigk with h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                rcases p287_3 (m.d 0 1) (by simp) with h289 | h289
                                · rcases p287_3 (m.d 0 2) (by simp) with h290 | h290
                                  · linarith only [h0, h290, hlam]
                                  · rcases p287_3 (m.d 0 3) (by simp) with h292 | h292
                                    · linarith only [h1, h292, hlam]
                                    · linarith only [h292, h3, hlam]
                                · linarith only [h0, h289, hlam]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h277, h279, hc01, hlam, hphi, ht0b, ht5b, p287_1, u5ehi4]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h279, hc01, hlam, hphi, ht0b, ht5b, p287_1, u5ehi4]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h2, h284, hc01, hlam, hphi, ht0b, ht5b, p287_1, u5ehi3]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h0, hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h3, hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h214, hlam, p287_1]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h275, hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h1, hlam, p287_1]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [hc02, hlam, hphi, ht23, p287_1, u3elo0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h279, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p287_1, u3elo2, u5ehi4]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h2, h284, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p287_1, u3elo2, u5ehi3]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p287_1]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h0, h214, h285, hc12, hlam, hphi, ht23, p287_1, u3elo2]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h277, hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h2, h214, h284, h285, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p287_1, u3elo2, u5ehi3]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h2, hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h0, h275, hc12, hlam, hphi, p287_1, u2elo4]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h278, hlam, p287_0]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [h279, hlam, p287_1]
                              · have p287_0 := h287c.1
                                have p287_1 := h287c.2.1
                                have p287_2 := h287c.2.2.1
                                have p287_3 := h287c.2.2.2
                                linarith only [hlam, p287_0]
                            · linarith only [h2, h214, h279, h284, h285, h286, hlam]
                          · linarith only [h277, h285, h3, hlam]
                        · linarith only [h278, h284, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h322 | h322
                    · linarith only [h0, h3, h322, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h0, h3, h324, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h326 | h326
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h327 | h327
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                            · rcases h0bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                rcases p329_3 (m.d 0 1) (by simp) with h331 | h331
                                · rcases p329_3 (m.d 0 2) (by simp) with h332 | h332
                                  · linarith only [h0, h332, hlam]
                                  · rcases p329_3 (m.d 0 3) (by simp) with h334 | h334
                                    · linarith only [h1, h334, hlam]
                                    · linarith only [h3, h334, hlam]
                                · linarith only [h0, h331, hlam]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h1, h326, hc01, hlam, hphi, ht0b, ht5b, p329_1, u5ehi3]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                rcases p329_3 (m.d 0 1) (by simp) with h339 | h339
                                · rcases p329_3 (m.d 0 2) (by simp) with h340 | h340
                                  · linarith only [h0, h340, hlam]
                                  · rcases p329_3 (m.d 0 3) (by simp) with h342 | h342
                                    · linarith only [h1, h342, hlam]
                                    · linarith only [h277, h342, hlam]
                                · linarith only [h339, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h2, h326, hc01, hlam, hphi, ht0b, ht5b, p329_1, u5ehi3]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h0, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h3, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h214, hlam, p329_1]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h275, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h1, hlam, p329_1]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, p329_1, u3elo0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h0, h214, h3, hc12, hlam, hphi, ht23, p329_1, u3elo2]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h2, h3, h326, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p329_1, u3elo2, u5ehi3]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h279, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p329_1]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h0, h214, h327, hc12, hlam, hphi, ht23, p329_1, u3elo2]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h277, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h279, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h2, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h0, h275, hc12, hlam, hphi, p329_1, u2elo4]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h278, hlam, p329_0]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [h278, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p329_1, u3elo2]
                              · have p329_0 := h329c.1
                                have p329_1 := h329c.2.1
                                have p329_2 := h329c.2.2.1
                                have p329_3 := h329c.2.2.2
                                linarith only [hlam, p329_0]
                            · linarith only [h1, h278, h3, h326, h328, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · linarith only [h1, h3, h326, h327, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · linarith only [h278, h326, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                  · linarith only [h277, h278, h370, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
                    · linarith only [h0, h3, h372, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                      · linarith only [h0, h214, h277, h278, h374, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h376 | h376
                        · linarith only [h214, h277, h278, h376, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h378 | h378
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h379 | h379
                            · linarith only [h277, h278, h379, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h0, h3, h379, hc12, hlam, hphi, ht23, u3elo4]
                          · linarith only [h0, h3, h378, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
                · linarith only [h277, h383, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                    · linarith only [h0, h3, h386, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
                      · linarith only [h0, h277, h3, h388, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
                        · linarith only [h1, h277, h390, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h392 | h392
                          · linarith only [h277, h3, h392, hc02, hlam, hphi, u2elo2]
                          · linarith only [h0, h3, h392, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                    · linarith only [h0, h3, h395, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                      · linarith only [h0, h2, h275, h3, h397, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                        · linarith only [h1, h383, h399, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                          · linarith only [h277, h3, h401, hc02, hlam, hphi, u2elo2]
                          · linarith only [h0, h3, h401, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h404 | h404
        · rcases m.htr 0 2 4 (by decide) (by decide) with h405 | h405
          · rcases m.htr 0 2 5 (by decide) (by decide) with h406 | h406
            · linarith only [h0, h2, h406, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 3 5 (by decide) (by decide) with h409 | h409
                · linarith only [h404, h406, h409, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h411 | h411
                  · linarith only [h405, h406, h411, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h2, h409, h413, hc23, hlam, hphi, u3elo4]
                    · linarith only [h404, h406, h413, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h416 | h416
                · linarith only [h405, h406, h408, h416, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h405, h406, h418, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
                    · linarith only [h0, h2, h416, h420, hc23, hlam, hphi, u3elo4]
                    · linarith only [h404, h406, h420, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h423 | h423
            · linarith only [h405, h423, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
              · linarith only [h404, h405, h425, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h427 | h427
                · linarith only [h404, h405, h427, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                    · linarith only [h0, h2, h425, h429, h430, hc23, hlam, hphi, u3elo3]
                    · linarith only [h404, h405, h430, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
                    · linarith only [h0, h2, h427, h433, hc23, hlam, hphi, u3elo4]
                    · linarith only [h404, h405, h433, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h436 | h436
          · rcases m.htr 0 2 5 (by decide) (by decide) with h437 | h437
            · linarith only [h404, h437, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h439 | h439
              · rcases m.htr 0 3 5 (by decide) (by decide) with h440 | h440
                · linarith only [h1, h2, h440, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                  · linarith only [h404, h436, h440, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                    · linarith only [h0, h404, h440, h444, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                      · linarith only [h1, h2, h440, h444, h446, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · linarith only [h1, h2, h444, h446, hc12, hlam, hphi, u2elo4]
              · linarith only [h404, h436, h439, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h450 | h450
            · linarith only [h436, h450, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
              · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
                · linarith only [h1, h2, h453, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                  · linarith only [h452, h453, h455, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · linarith only [h0, h436, h452, h453, h457, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                      · linarith only [h0, h436, h452, h453, h459, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · linarith only [h1, h2, h457, h459, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h462 | h462
                · linarith only [h452, h462, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
                    · linarith only [h0, h404, h465, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h467 | h467
                      · linarith only [h1, h2, h465, h467, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h2, h467, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
                    · linarith only [h0, h2, h462, h470, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                      · linarith only [h1, h2, h462, h470, h472, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                      · linarith only [h1, h2, h470, h472, hc12, hlam, hphi, u2elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h476 | h476
    · rcases m.htr 0 1 5 (by decide) (by decide) with h477 | h477
      · linarith only [h0, h477, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h479 | h479
        · rcases m.htr 0 2 4 (by decide) (by decide) with h480 | h480
          · rcases m.htr 0 2 5 (by decide) (by decide) with h481 | h481
            · rcases m.htr 0 3 4 (by decide) (by decide) with h482 | h482
              · rcases m.htr 0 3 5 (by decide) (by decide) with h483 | h483
                · linarith only [h0, h476, h483, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h485 | h485
                  · linarith only [h0, h476, h482, h485, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h488 | h488
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                        · linarith only [h476, h477, h483, h488, h489, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h476, h477, h487, h489, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h476, h487, h488, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h487, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h494 | h494
                · linarith only [h482, h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h496 | h496
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h499 | h499
                        · linarith only [h476, h477, h494, h498, h499, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h476, h477, h497, h499, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h476, h482, h496, h497, h498, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u3elo3, u5ehi4]
                    · linarith only [h0, h497, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h506 | h506
                        · linarith only [h476, h477, h494, h505, h506, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · linarith only [h476, h477, h506, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h476, h481, h504, h505, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h481, h504, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h511 | h511
              · rcases m.htr 0 3 5 (by decide) (by decide) with h512 | h512
                · linarith only [h0, h476, h481, h512, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h514 | h514
                  · linarith only [h0, h476, h481, h511, h514, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
                      · linarith only [h0, h476, h481, h516, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h476, h516, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h476, h516, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
                · linarith only [h511, h521, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h523 | h523
                  · linarith only [h480, h481, h523, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
                      · linarith only [h0, h476, h481, h525, h526, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h476, h525, h526, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h476, h525, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h530 | h530
            · linarith only [h480, h530, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h532 | h532
              · linarith only [h0, h476, h480, h532, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
                · linarith only [h532, h534, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h537 | h537
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
                      · linarith only [h0, h476, h530, h537, h538, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h476, h537, h538, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h476, h537, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h543 | h543
                      · linarith only [h530, h543, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h476, h542, h543, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h476, h542, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h476, h479, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h548 | h548
      · linarith only [h476, h548, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h550 | h550
        · rcases m.htr 0 2 4 (by decide) (by decide) with h551 | h551
          · rcases m.htr 0 2 5 (by decide) (by decide) with h552 | h552
            · rcases m.htr 0 3 4 (by decide) (by decide) with h553 | h553
              · rcases m.htr 0 3 5 (by decide) (by decide) with h554 | h554
                · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h558 | h558
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                            · linarith only [h550, h560, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · linarith only [h554, h560, hc23, hlam, hphi, u3elo0]
                          · linarith only [h476, h553, h559, hc23, hlam, hphi, u3elo1]
                        · linarith only [h476, h554, h558, hlam]
                      · linarith only [h0, h557, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h550, h553, h555, h556, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h567 | h567
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h568 | h568
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h570 | h570
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h571 | h571
                            · linarith only [h550, h571, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · linarith only [h476, h554, h571, hc23, hlam, hphi, u3elo1]
                          · linarith only [h476, h553, h570, hc23, hlam, hphi, u3elo1]
                        · linarith only [h476, h554, h569, hlam]
                      · linarith only [h0, h552, h568, hlam]
                    · linarith only [h0, h552, h567, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                  · linarith only [h553, h554, h578, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                        · linarith only [h554, h582, hc03, hlam, hphi, u3elo1]
                        · linarith only [h476, h582, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h552, h581, hlam]
                    · linarith only [h0, h552, h580, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h587 | h587
                · linarith only [h553, h587, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h589 | h589
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h591 | h591
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h592 | h592
                        · linarith only [h587, h592, hc03, hlam, hphi, u3elo1]
                        · linarith only [h476, h592, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h551, h589, h591, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · linarith only [h0, h551, h589, h590, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h598 | h598
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h599 | h599
                        · linarith only [h587, h599, hc03, hlam, hphi, u3elo1]
                        · linarith only [h476, h599, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h552, h598, hlam]
                    · linarith only [h0, h552, h597, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h604 | h604
              · rcases m.htr 0 3 5 (by decide) (by decide) with h605 | h605
                · linarith only [h550, h552, h605, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h607 | h607
                  · linarith only [h550, h552, h604, h607, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h609 | h609
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                      · linarith only [h552, h610, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h610, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h609, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h614 | h614
                · linarith only [h551, h552, h604, h614, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h616 | h616
                  · linarith only [h551, h552, h616, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h619 | h619
                      · linarith only [h552, h619, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h619, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h618, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h623 | h623
            · linarith only [h551, h623, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h625 | h625
              · linarith only [h550, h551, h625, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
                · linarith only [h550, h551, h627, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
                      · linarith only [h623, h631, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h631, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h630, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h636 | h636
                      · linarith only [h623, h636, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h636, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h635, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h640 | h640
          · rcases m.htr 0 2 5 (by decide) (by decide) with h641 | h641
            · linarith only [h550, h641, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h643 | h643
              · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
                · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                  · linarith only [h550, h640, h645, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
                    · linarith only [h550, h647, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h647, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h650 | h650
                  · linarith only [h640, h641, h650, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                    · linarith only [h550, h652, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h652, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h550, h640, h643, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h656 | h656
            · linarith only [h640, h656, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h658 | h658
              · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
                · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                    · linarith only [h550, h661, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h661, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h664 | h664
                    · linarith only [h0, h550, h664, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h664, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h667 | h667
                  · linarith only [h658, h659, h667, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h669 | h669
                    · linarith only [h0, h550, h669, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h669, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h672 | h672
                · linarith only [h658, h672, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h674 | h674
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h675 | h675
                    · linarith only [h0, h550, h675, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h675, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
                    · linarith only [h0, h550, h678, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h678, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
