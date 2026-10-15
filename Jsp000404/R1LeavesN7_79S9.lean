import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
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
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
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
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h10, h14, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h14, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                            · linarith only [h12, h13, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h12, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                        · linarith only [h11, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                              · linarith only [h25, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h21, h23, h25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · linarith only [h24, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                          · linarith only [h21, h23, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                        · linarith only [h22, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h21, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h33, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                          · linarith only [h1, h38, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h1, h40, h7, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                              · linarith only [h36, h42, h7, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                                · linarith only [h44, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                · linarith only [h35, h42, h44, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                        · linarith only [h37, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h36, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                          · linarith only [h1, h51, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                            · linarith only [h1, h33, h53, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h49, h55, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                · linarith only [h35, h5, h57, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                                  · linarith only [h35, h59, h7, hc34, hlam, hphi, u3ehi0]
                                  · linarith only [h1, h49, h59, h7, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h50, h6, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h49, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h66 | h66
            · rcases m.htr 0 2 5 (by decide) (by decide) with h67 | h67
              · linarith only [h4, h67, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
                · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h4, h66, h71, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                      · linarith only [h4, h73, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                        · linarith only [h0, h67, h75, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                              · linarith only [h4, h66, h79, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                              · linarith only [h1, h4, h66, h77, h79, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h4, h70, h78, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · linarith only [h4, h69, h77, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                  · linarith only [h69, h70, hc35, hlam, hphi, u3ehi3]
                · linarith only [h4, h66, h69, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h86 | h86
              · linarith only [h66, h86, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h88 | h88
                · rcases m.htr 0 3 5 (by decide) (by decide) with h89 | h89
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                      · linarith only [h0, h66, h91, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                        · linarith only [h0, h86, h93, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                                  · linarith only [h1, h95, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h66, h90, h97, h99, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                                · linarith only [h66, h90, h98, hlam]
                              · linarith only [h1, h4, h96, h97, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h95, h96, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h4, h88, h95, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                      · linarith only [h0, h106, h4, h86, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h0, h108, h86, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                                · linarith only [h112, h113, h66, h90, hc02, hlam, hphi, u2elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                                  · linarith only [h1, h110, h113, h115, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      rcases p117_3 (m.d 0 1) (by simp) with h119 | h119
                                      · rcases p117_3 (m.d 0 2) (by simp) with h120 | h120
                                        · linarith only [h0, h120, hlam]
                                        · rcases p117_3 (m.d 0 3) (by simp) with h122 | h122
                                          · linarith only [h1, h122, hlam]
                                          · linarith only [h122, h4, hlam]
                                      · linarith only [h0, h119, hlam]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p117_1, u3ehi0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h110, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p117_1, u3ehi3]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p117_1, u5ehi0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h0, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h4, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h66, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h86, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h1, hlam, p117_1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h0, h4, hc12, hlam, hphi, p117_1, u2elo2]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h110, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p117_1, u2elo2, u3ehi3]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p117_1, u2elo2, u5ehi1]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h2, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h0, h66, hc12, hlam, hphi, p117_1, u2elo3]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h88, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h90, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h3, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h0, h86, hc12, hlam, hphi, p117_1, u2elo4]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h89, hlam, p117_0]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [h4, h89, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p117_1, u2elo2]
                                    · have p117_0 := h117c.1
                                      have p117_1 := h117c.2.1
                                      have p117_2 := h117c.2.2.1
                                      have p117_3 := h117c.2.2.2
                                      linarith only [hlam, p117_0]
                              · linarith only [h1, h111, h112, h4, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h110, h111, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h110, h4, h88, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                  · linarith only [h88, h89, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h153 | h153
                  · linarith only [h153, h88, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                      · linarith only [h0, h156, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h0, h158, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                          · linarith only [h1, h160, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                            · linarith only [h1, h153, h162, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                              · linarith only [h164, h88, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                                  · rcases h0bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      rcases p168_3 (m.d 0 1) (by simp) with h170 | h170
                                      · rcases p168_3 (m.d 0 2) (by simp) with h171 | h171
                                        · linarith only [h0, h171, hlam]
                                        · rcases p168_3 (m.d 0 3) (by simp) with h173 | h173
                                          · linarith only [h1, h173, hlam]
                                          · linarith only [h173, h4, hlam]
                                      · linarith only [h0, h170, hlam]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p168_1, u3ehi1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h155, hc01, hlam, hphi, ht0b, ht5b, p168_1, u5ehi0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p168_1, u5ehi0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h0, hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h4, hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h66, hlam, p168_1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h86, hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h1, hlam, p168_1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h0, h4, hc12, hlam, hphi, p168_1, u2elo2]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h88, hlam, p168_1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h153, hlam, p168_1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h2, hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h0, h66, hc12, hlam, hphi, p168_1, u2elo3]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h66, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p168_1, u2elo3, u3ehi0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h162, h3, h66, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p168_1, u2elo3, u3ehi1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h3, hlam, p168_0]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h0, h86, hc12, hlam, hphi, p168_1, u2elo4]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h1, h86, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p168_1, u2elo4, u3ehi1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [h155, hlam, p168_1]
                                    · have p168_0 := h168c.1
                                      have p168_1 := h168c.2.1
                                      have p168_2 := h168c.2.2.1
                                      have p168_3 := h168c.2.2.2
                                      linarith only [hlam, p168_0]
                                  · linarith only [h164, h167, hc45, hlam, hphi, ht34, u3ehi2]
                                · linarith only [h155, h166, h66, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                      · linarith only [h0, h202, h4, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h0, h204, h4, h86, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                          · linarith only [h1, h206, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                            · linarith only [h1, h153, h208, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                              · linarith only [h210, h88, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h212 | h212
                                · linarith only [h1, h155, h212, h88, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h214 | h214
                                  · linarith only [h1, h155, h214, h88, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h1, h214, h88, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h217 | h217
          · rcases m.htr 0 2 4 (by decide) (by decide) with h218 | h218
            · rcases m.htr 0 2 5 (by decide) (by decide) with h219 | h219
              · linarith only [h0, h219, h3, hlam]
              · linarith only [h217, h219, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h217, h218, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h223 | h223
            · rcases m.htr 0 2 5 (by decide) (by decide) with h224 | h224
              · linarith only [h217, h224, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h226 | h226
                · rcases m.htr 0 3 5 (by decide) (by decide) with h227 | h227
                  · linarith only [h1, h227, h3, hlam]
                  · linarith only [h226, h227, hc35, hlam, hphi, u3ehi3]
                · linarith only [h217, h223, h226, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h231 | h231
              · linarith only [h217, h231, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h233 | h233
                · rcases m.htr 0 3 5 (by decide) (by decide) with h234 | h234
                  · linarith only [h1, h234, h3, hlam]
                  · linarith only [h233, h234, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h237 | h237
                  · linarith only [h233, h237, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
                    · linarith only [h2, h239, h3, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h241 | h241
                      · linarith only [h217, h241, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
                        · linarith only [h0, h231, h243, h3, hlam]
                        · linarith only [h1, h243, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h246 | h246
        · rcases m.htr 0 2 3 (by decide) (by decide) with h247 | h247
          · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
            · linarith only [h0, h2, h248, hlam]
            · linarith only [h247, h248, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h251 | h251
            · linarith only [h2, h246, h247, h251, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h253 | h253
              · linarith only [h247, h253, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h255 | h255
                · linarith only [h1, h2, h255, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                  · linarith only [h255, h257, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                      · linarith only [h247, h260, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h0, h2, h251, h253, h262, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                          · linarith only [h1, h2, h251, h255, h264, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi0]
                          · linarith only [h1, h2, h264, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h1, h2, h259, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h268 | h268
          · rcases m.htr 0 2 4 (by decide) (by decide) with h269 | h269
            · linarith only [h0, h2, h269, hlam]
            · linarith only [h268, h269, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h272 | h272
            · linarith only [h0, h2, h268, h272, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
              · linarith only [h268, h274, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
                · linarith only [h1, h2, h276, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h278 | h278
                  · linarith only [h276, h278, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                      · linarith only [h268, h281, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h283 | h283
                        · linarith only [h1, h246, h274, h281, h283, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h246, h283, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi1]
                    · linarith only [h1, h2, h280, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h287 | h287
      · rcases m.htr 0 1 5 (by decide) (by decide) with h288 | h288
        · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
          · linarith only [h0, h1, h289, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h291 | h291
            · rcases m.htr 0 2 5 (by decide) (by decide) with h292 | h292
              · linarith only [h289, h292, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h294 | h294
                · rcases m.htr 0 3 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h296 | h296
                    · linarith only [h289, h291, h296, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
                      · linarith only [h289, h291, h298, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1, h288, h298, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                  · linarith only [h294, h295, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h288, h291, h292, h294, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h303 | h303
              · linarith only [h289, h303, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h305 | h305
                · rcases m.htr 0 3 5 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h308 | h308
                      · linarith only [h0, h1, h289, h308, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1, h287, h307, h308, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                      · linarith only [h0, h1, h311, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h311, hc12, hlam, hphi, u2elo2]
                  · linarith only [h305, h306, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h287, h305, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h316 | h316
          · linarith only [h0, h1, h316, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
            · rcases m.htr 0 2 5 (by decide) (by decide) with h319 | h319
              · linarith only [h316, h319, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h321 | h321
                · rcases m.htr 0 3 5 (by decide) (by decide) with h322 | h322
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
                    · linarith only [h316, h318, h323, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                      · linarith only [h316, h325, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h325, hc12, hlam, hphi, u2elo2]
                  · linarith only [h321, h322, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h318, h321, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h330 | h330
              · linarith only [h318, h330, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
                · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                    · linarith only [h287, h288, h334, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                      · linarith only [h0, h1, h336, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h336, hc12, hlam, hphi, u2elo2]
                  · linarith only [h332, h333, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h287, h332, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h341 | h341
        · rcases m.htr 0 2 3 (by decide) (by decide) with h342 | h342
          · linarith only [h0, h1, h342, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h344 | h344
            · linarith only [h0, h287, h342, h344, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h346 | h346
              · linarith only [h342, h346, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h348 | h348
                · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h350 | h350
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
                      · linarith only [h342, h351, hc02, hlam, hphi, u2elo1]
                      · linarith only [h1, h341, h351, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                    · linarith only [h287, h341, h350, hlam]
                  · linarith only [h348, h349, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                  · linarith only [h348, h356, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h341, h356, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h359 | h359
          · linarith only [h0, h1, h359, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h361 | h361
            · linarith only [h0, h287, h359, h361, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h363 | h363
              · linarith only [h359, h363, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h365 | h365
                · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h367 | h367
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                      · linarith only [h0, h1, h359, h368, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h368, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                      · linarith only [h0, h359, h365, h371, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1, h371, hc12, hlam, hphi, u2elo2]
                  · linarith only [h365, h366, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h375 | h375
                  · linarith only [h365, h375, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h377 | h377
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
                      · linarith only [h0, h1, h378, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h378, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
                      · linarith only [h0, h1, h381, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h381, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h384 | h384
    · linarith only [h0, h384, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h386 | h386
      · rcases m.htr 0 1 5 (by decide) (by decide) with h387 | h387
        · linarith only [h0, h387, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h389 | h389
          · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
            · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
              · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
                · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                    · linarith only [h0, h386, h394, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                          · linarith only [h384, h386, h396, h398, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                          · linarith only [h384, h386, h389, h392, h398, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h391, h397, hlam]
                      · linarith only [h0, h391, h396, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · linarith only [h392, h393, hc35, hlam, hphi, u3ehi3]
                · linarith only [h384, h386, h392, hlam]
              · linarith only [h389, h391, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h389, h390, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
              · linarith only [h389, h408, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h410 | h410
                · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h412 | h412
                    · linarith only [h0, h386, h412, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
                      · linarith only [h0, h389, h414, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h386, h410, h414, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h410, h411, hc35, hlam, hphi, u3ehi3]
                · linarith only [h384, h386, h410, hlam]
            · linarith only [h0, h386, h407, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h420 | h420
        · linarith only [h0, h420, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h422 | h422
          · rcases m.htr 0 2 4 (by decide) (by decide) with h423 | h423
            · rcases m.htr 0 2 5 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 3 5 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
                              · linarith only [h422, h432, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h384, h425, h428, h432, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · linarith only [h384, h426, h431, hlam]
                          · linarith only [h384, h425, h430, hlam]
                        · linarith only [h384, h426, h428, h429, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                      · linarith only [h0, h422, h425, h428, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h442 | h442
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h443 | h443
                              · linarith only [h422, h443, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h0, h422, h425, h443, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · linarith only [h384, h426, h442, hlam]
                          · linarith only [h384, h425, h441, hlam]
                        · linarith only [h0, h424, h440, hlam]
                      · linarith only [h0, h424, h439, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                  · linarith only [h425, h426, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h451 | h451
                  · linarith only [h425, h451, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h453 | h453
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h455 | h455
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                          · linarith only [h425, h454, h456, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h458 | h458
                            · linarith only [h456, h458, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
                              · linarith only [h456, h460, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                                · linarith only [h0, h423, h462, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                · linarith only [h0, h423, h453, h460, h462, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                        · linarith only [h0, h423, h453, h455, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                      · linarith only [h0, h422, h454, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                          · linarith only [h422, h425, h467, h469, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h471 | h471
                            · linarith only [h422, h451, h467, h471, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h473 | h473
                              · linarith only [h422, h469, h473, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h475 | h475
                                · linarith only [h0, h423, h453, h475, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h477 | h477
                                  · linarith only [h423, h453, h473, h477, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h422, h425, h477, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h424, h468, hlam]
                      · linarith only [h0, h424, h467, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h422, h424, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h422, h423, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h484 | h484
            · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
              · linarith only [h422, h485, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h487 | h487
                · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h422, h484, h489, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                      · linarith only [h386, h422, h484, h491, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h491, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h487, h488, hc35, hlam, hphi, u3ehi3]
                · linarith only [h422, h484, h487, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h496 | h496
              · linarith only [h484, h496, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h498 | h498
                · rcases m.htr 0 3 5 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h501 | h501
                      · linarith only [h422, h501, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h501, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                      · linarith only [h0, h422, h504, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h504, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h498, h499, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                  · linarith only [h498, h508, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
                      · linarith only [h0, h422, h511, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h511, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h514 | h514
                      · linarith only [h0, h422, h514, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h514, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_M_LR_L_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h1, h10, h12, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h12, h6, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h15, h6, h9, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                        · linarith only [h17, h6, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h19, h7, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                            · linarith only [h0, h1, h19, h21, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h15, h21, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h3, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h2, h6, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                · linarith only [h0, h1, h26, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h0, h1, h28, h6, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                            · linarith only [h0, h1, h31, h34, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h1, h31, h33, h34, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h26, h33, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h26, h31, h32, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1, h30, h31, h4, h6, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                        · linarith only [h0, h1, h30, h41, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h40, h41, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h1, h4, h40, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
            · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
              · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                      · linarith only [h0, h4, h46, h47, h51, hlam, hphi, u0ehi9, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h0, h48, h51, h53, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h4, h46, h53, hc23, hc34, hlam, hphi]
                    · linarith only [h4, h46, h50, hc13, hc34, hlam, hphi]
                  · linarith only [h48, h49, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h2, h47, h48, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                · linarith only [h0, h1, h47, h59, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                  · linarith only [h0, h1, h47, h61, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                      · linarith only [h0, h1, h4, h64, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                            · rcases h2bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                rcases p69_3 (m.d 0 2) (by simp) with h71 | h71
                                · rcases p69_3 (m.d 1 2) (by simp) with h72 | h72
                                  · linarith only [h0, h72, hlam]
                                  · rcases p69_3 (m.d 2 3) (by simp) with h74 | h74
                                    · linarith only [h1, h74, hlam]
                                    · linarith only [h47, h74, hlam]
                                · linarith only [h0, h71, hlam]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h61, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h61, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h47, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h59, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h61, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h1, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h64, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h2, h61, h64, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h2, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h2, h47, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h0, h2, h61, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h3, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p69_1, u5elo2]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h66, hlam, p69_0]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [h67, hlam, p69_1]
                              · have p69_0 := h69c.1
                                have p69_1 := h69c.2.1
                                have p69_2 := h69c.2.2.1
                                have p69_3 := h69c.2.2.2
                                linarith only [hlam, p69_0]
                            · linarith only [h4, h46, h68, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                          · linarith only [h61, h64, h66, h67, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h4, h46, h66, hc23, hc34, hlam, hphi]
                    · linarith only [h4, h46, h63, hc13, hc34, hlam, hphi]
            · linarith only [h46, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h1, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
        · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
          · linarith only [h1, h108, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
              · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                · linarith only [h1, h110, h112, h2, hc12, hlam, hphi, ht01, u0ehi9]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                      · linarith only [h108, h110, h116, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h0, h111, h118, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h110, h116, h118, h2, hc23, hc34, hlam, hphi]
                    · linarith only [h108, h110, h115, hc13, hc34, hlam, hphi]
                  · linarith only [h107, h114, h2, hc12, hc24, hlam, hphi]
              · linarith only [h1, h111, h2, hc12, hc24, hlam, hphi]
            · linarith only [h110, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h1, h107, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h126 | h126
      · rcases m.htr 0 2 5 (by decide) (by decide) with h127 | h127
        · rcases m.htr 0 3 4 (by decide) (by decide) with h128 | h128
          · rcases m.htr 0 3 5 (by decide) (by decide) with h129 | h129
            · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
              · linarith only [h1, h126, h130, hc12, hlam, hphi, ht01, u0ehi8]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                          · linarith only [h0, h132, h137, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                            · linarith only [h135, h137, h139, hlam]
                            · rcases h2bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h1, hc12, hc23, hlam, hphi, p141_1]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h1, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                rcases p141_3 (m.d 0 2) (by simp) with h145 | h145
                                · rcases p141_3 (m.d 1 2) (by simp) with h146 | h146
                                  · linarith only [h0, h146, hlam]
                                  · linarith only [h132, h146, hlam]
                                · linarith only [h145, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                rcases p141_3 (m.d 0 2) (by simp) with h150 | h150
                                · rcases p141_3 (m.d 1 2) (by simp) with h151 | h151
                                  · linarith only [h0, h151, hlam]
                                  · linarith only [h133, h151, hlam]
                                · linarith only [h150, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h0, hlam, p141_1]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h130, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h0, h135, hc34, hlam, hphi, ht0b, ht45, ht5b, p141_1, u0elo0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h0, h135, h137, hc34, hlam, hphi, ht0b, ht45, ht5b, p141_1, u0elo0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p141_1, u0ehi6]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                rcases p141_3 (m.d 0 2) (by simp) with h161 | h161
                                · linarith only [h1, h161, hlam]
                                · linarith only [h0, h161, hlam]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                rcases p141_3 (m.d 0 2) (by simp) with h165 | h165
                                · linarith only [h1, h165, hlam]
                                · linarith only [h126, h165, hlam]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                rcases p141_3 (m.d 0 2) (by simp) with h168 | h168
                                · linarith only [h1, h168, hlam]
                                · linarith only [h127, h168, hlam]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h126, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h132, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h135, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h137, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h127, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h133, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h136, hlam, p141_0]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [h135, hc34, hlam, hphi, ht45, p141_1, u5elo2]
                              · have p141_0 := h141c.1
                                have p141_1 := h141c.2.1
                                have p141_2 := h141c.2.2.1
                                have p141_3 := h141c.2.2.2
                                linarith only [hlam, p141_0]
                        · linarith only [h0, h1, h126, h133, h134, h136, hlam, hphi, u0ehi8, u0elo0]
                      · linarith only [h1, h126, h135, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                    · linarith only [h130, h133, h134, hc25, hlam, hphi, u5elo3]
                  · linarith only [h132, h133, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h1, h126, h132, hc12, hc23, hlam, hphi]
            · linarith only [h128, h129, hc34, hlam, hphi, ht45, u5elo3]
          · linarith only [h1, h126, h128, hlam]
        · linarith only [h126, h127, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h189 | h189
        · rcases m.htr 0 3 4 (by decide) (by decide) with h190 | h190
          · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
            · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
              · linarith only [h1, h189, h192, hc12, hlam, hphi, ht01, u0ehi9]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                · linarith only [h0, h126, h189, h194, hlam, hphi, u0ehi9, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                            · rcases h2bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h126, h198, hc12, hc23, hlam, hphi, p202_1]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h1, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h126, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                rcases p202_3 (m.d 0 2) (by simp) with h207 | h207
                                · rcases p202_3 (m.d 1 2) (by simp) with h208 | h208
                                  · linarith only [h0, h208, hlam]
                                  · linarith only [h196, h208, hlam]
                                · linarith only [h207, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h0, hlam, p202_1]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h192, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h194, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h0, h199, h201, hc45, hlam, hphi, ht0b, ht5b, p202_1, u0elo0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p202_1, u0ehi6]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                rcases p202_3 (m.d 0 2) (by simp) with h218 | h218
                                · linarith only [h1, h218, hlam]
                                · linarith only [h0, h218, hlam]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h126, h189, hc23, hlam, hphi, ht01, ht12, p202_1, u0ehi9]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                rcases p202_3 (m.d 0 2) (by simp) with h223 | h223
                                · linarith only [h1, h223, hlam]
                                · linarith only [h189, h223, hlam]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h189, hc24, hlam, hphi, ht01, ht12, p202_1, u0ehi9]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                rcases p202_3 (m.d 0 2) (by simp) with h227 | h227
                                · linarith only [h126, h227, hlam]
                                · linarith only [h0, h227, hlam]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h198, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                rcases p202_3 (m.d 0 2) (by simp) with h232 | h232
                                · linarith only [h126, h232, hlam]
                                · linarith only [h189, h232, hlam]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h189, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h196, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h199, hlam, p202_0]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [h200, hlam, p202_1]
                              · have p202_0 := h202c.1
                                have p202_1 := h202c.2.1
                                have p202_2 := h202c.2.2.1
                                have p202_3 := h202c.2.2.2
                                linarith only [hlam, p202_0]
                            · linarith only [h0, h196, h200, h201, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h126, h189, h200, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9, u5elo4]
                        · linarith only [h1, h189, h197, h199, hc13, hlam, hphi, ht01, u0ehi9]
                      · linarith only [h1, h189, h198, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h191, h192, h196, h197, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1, h189, h196, hc12, hc23, hlam, hphi]
            · linarith only [h190, h191, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h247 | h247
            · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
              · linarith only [h0, h1, h248, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                · linarith only [h0, h126, h189, h250, hlam, hphi, u0ehi9, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h253 | h253
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                      · linarith only [h190, h254, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                      · linarith only [h1, h189, h254, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h190, h247, h253, hc13, hc34, hlam, hphi]
                  · linarith only [h1, h189, h252, hc12, hc23, hlam, hphi]
            · linarith only [h1, h189, h247, hc25, hlam, hphi, u5elo3]
        · linarith only [h189, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h261 | h261
    · rcases m.htr 0 2 4 (by decide) (by decide) with h262 | h262
      · rcases m.htr 0 2 5 (by decide) (by decide) with h263 | h263
        · rcases m.htr 0 3 4 (by decide) (by decide) with h264 | h264
          · rcases m.htr 0 3 5 (by decide) (by decide) with h265 | h265
            · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
              · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h269 | h269
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                            · linarith only [h261, h270, h273, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h261, h270, h272, h273, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h276 | h276
                            · linarith only [h261, h264, h272, h276, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h2bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h0, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h271, hc35, hlam, hphi, ht0b, ht5b, p278_1, u0elo1]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                rcases p278_3 (m.d 0 2) (by simp) with h282 | h282
                                · rcases p278_3 (m.d 1 2) (by simp) with h283 | h283
                                  · rcases p278_3 (m.d 2 3) (by simp) with h284 | h284
                                    · linarith only [h261, h284, hlam]
                                    · linarith only [h270, h284, hlam]
                                  · linarith only [h267, h283, hlam]
                                · linarith only [h282, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                rcases p278_3 (m.d 0 2) (by simp) with h289 | h289
                                · rcases p278_3 (m.d 1 2) (by simp) with h290 | h290
                                  · rcases p278_3 (m.d 2 3) (by simp) with h291 | h291
                                    · linarith only [h261, h291, hlam]
                                    · linarith only [h271, h291, hlam]
                                  · linarith only [h268, h290, hlam]
                                · linarith only [h289, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p278_1, u0ehi6]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                rcases p278_3 (m.d 0 2) (by simp) with h298 | h298
                                · linarith only [h0, h298, hlam]
                                · linarith only [h261, h298, hlam]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                rcases p278_3 (m.d 0 2) (by simp) with h301 | h301
                                · linarith only [h0, h301, hlam]
                                · linarith only [h262, h301, hlam]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                rcases p278_3 (m.d 0 2) (by simp) with h304 | h304
                                · linarith only [h0, h304, hlam]
                                · linarith only [h263, h304, hlam]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h261, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h266, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h261, h270, hc34, hlam, hphi, ht0b, ht45, ht5b, p278_1, u0elo1]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h261, h271, h276, hc34, hlam, hphi, ht0b, ht45, ht5b, p278_1, u0elo1]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h262, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h267, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h270, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h272, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h263, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h268, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h271, hlam, p278_0]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [h268, h270, hc34, hlam, hphi, ht45, p278_1, u5elo1]
                              · have p278_0 := h278c.1
                                have p278_1 := h278c.2.1
                                have p278_2 := h278c.2.2.1
                                have p278_3 := h278c.2.2.2
                                linarith only [hlam, p278_0]
                        · linarith only [h261, h265, h270, h271, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                        · linarith only [h261, h264, h270, h323, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                            · rcases h2bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h0, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 2) (by simp) with h330 | h330
                                · rcases p327_3 (m.d 1 2) (by simp) with h331 | h331
                                  · rcases p327_3 (m.d 2 3) (by simp) with h332 | h332
                                    · linarith only [h332, hlam, p327_0]
                                    · rcases p327_3 (m.d 2 4) (by simp) with h334 | h334
                                      · linarith only [h262, h334, hlam]
                                      · linarith only [h270, h334, hlam]
                                  · linarith only [h266, h331, hlam]
                                · linarith only [h330, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h325, hc45, hlam, hphi, ht0b, ht5b, p327_1, u0elo1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 2) (by simp) with h340 | h340
                                · rcases p327_3 (m.d 1 2) (by simp) with h341 | h341
                                  · rcases p327_3 (m.d 2 3) (by simp) with h342 | h342
                                    · linarith only [h261, h342, hlam]
                                    · rcases p327_3 (m.d 2 4) (by simp) with h344 | h344
                                      · linarith only [h262, h344, hlam]
                                      · linarith only [h325, h344, hlam]
                                  · linarith only [h268, h341, hlam]
                                · linarith only [h340, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h261, h264, h323, h326, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 2) (by simp) with h351 | h351
                                · linarith only [h0, h351, hlam]
                                · linarith only [h261, h351, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 2) (by simp) with h354 | h354
                                · linarith only [h0, h354, hlam]
                                · linarith only [h262, h354, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 2) (by simp) with h357 | h357
                                · linarith only [h0, h357, hlam]
                                · linarith only [h263, h357, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h261, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h266, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h270, hlam, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h323, hlam, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h262, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h267, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h262, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1, u0elo1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h264, h270, hc25, hlam, hphi, ht0b, ht5b, p327_1, u0elo2]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h263, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h268, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p327_1, u5elo2]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h325, hlam, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                            · linarith only [h270, h326, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h376 | h376
                            · linarith only [h261, h264, h325, h376, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h270, h376, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                      · linarith only [h261, h265, h266, h269, h379, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                        · linarith only [h266, h269, h381, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
                            · rcases h2bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h0, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 2) (by simp) with h388 | h388
                                · rcases p385_3 (m.d 1 2) (by simp) with h389 | h389
                                  · rcases p385_3 (m.d 2 3) (by simp) with h390 | h390
                                    · linarith only [h390, hlam, p385_0]
                                    · rcases p385_3 (m.d 2 4) (by simp) with h392 | h392
                                      · linarith only [h262, h392, hlam]
                                      · linarith only [h379, h392, hlam]
                                  · linarith only [h266, h389, hlam]
                                · linarith only [h388, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h383, hc45, hlam, hphi, ht0b, ht5b, p385_1, u0elo1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 2) (by simp) with h398 | h398
                                · rcases p385_3 (m.d 1 2) (by simp) with h399 | h399
                                  · rcases p385_3 (m.d 2 3) (by simp) with h400 | h400
                                    · linarith only [h261, h400, hlam]
                                    · rcases p385_3 (m.d 2 4) (by simp) with h402 | h402
                                      · linarith only [h262, h402, hlam]
                                      · linarith only [h383, h402, hlam]
                                  · linarith only [h268, h399, hlam]
                                · linarith only [h398, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h261, h264, h269, h384, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 2) (by simp) with h409 | h409
                                · linarith only [h0, h409, hlam]
                                · linarith only [h261, h409, hlam]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 2) (by simp) with h412 | h412
                                · linarith only [h0, h412, hlam]
                                · linarith only [h262, h412, hlam]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 2) (by simp) with h415 | h415
                                · linarith only [h0, h415, hlam]
                                · linarith only [h263, h415, hlam]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h261, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h266, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h379, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h381, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h262, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h267, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h262, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p385_1, u0elo1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h264, h379, hc25, hlam, hphi, ht0b, ht5b, p385_1, u0elo2]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h263, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h268, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p385_1, u5elo2]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h383, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                            · linarith only [h379, h384, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h434 | h434
                            · linarith only [h261, h264, h383, h434, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h379, h434, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h268, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]
                · linarith only [h0, h267, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h266, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h265, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
            · rcases m.htr 1 2 3 (by decide) (by decide) with h442 | h442
              · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                · rcases m.htr 1 2 5 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                      · linarith only [h261, h264, h441, h446, hlam, hphi, u0ehi9, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h450 | h450
                            · rcases h2bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h0, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h448, hc35, hlam, hphi, ht0b, ht5b, p451_1, u0elo1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h446, h448, h450, hc45, hlam, hphi, ht0b, ht5b, p451_1, u0elo1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                rcases p451_3 (m.d 0 2) (by simp) with h456 | h456
                                · rcases p451_3 (m.d 1 2) (by simp) with h457 | h457
                                  · rcases p451_3 (m.d 2 3) (by simp) with h458 | h458
                                    · linarith only [h261, h458, hlam]
                                    · linarith only [h448, h458, hlam]
                                  · linarith only [h444, h457, hlam]
                                · linarith only [h456, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p451_1, u0ehi6]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                rcases p451_3 (m.d 0 2) (by simp) with h465 | h465
                                · linarith only [h0, h465, hlam]
                                · linarith only [h261, h465, hlam]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                rcases p451_3 (m.d 0 2) (by simp) with h468 | h468
                                · linarith only [h0, h468, hlam]
                                · linarith only [h262, h468, hlam]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                rcases p451_3 (m.d 0 2) (by simp) with h471 | h471
                                · linarith only [h0, h471, hlam]
                                · linarith only [h263, h471, hlam]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h261, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h442, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h446, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h262, h446, h448, h450, hc45, hlam, hphi, ht0b, ht5b, p451_1, u0elo1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h262, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h443, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h262, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p451_1, u0elo1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h262, h448, h450, hc45, hlam, hphi, ht0b, ht5b, p451_1, u0elo1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h263, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h444, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h448, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h449, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                            · linarith only [h264, h441, h450, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                          · linarith only [h446, h448, h449, hc35, hlam, hphi, u5elo4]
                        · linarith only [h264, h441, h448, hc23, hc34, hlam, hphi]
                    · linarith only [h264, h441, h445, hc13, hc34, hlam, hphi]
                  · linarith only [h0, h444, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]
                · linarith only [h0, h443, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h442, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h441, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h261, h263, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h498 | h498
        · rcases m.htr 0 3 4 (by decide) (by decide) with h499 | h499
          · linarith only [h261, h262, h499, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h501 | h501
            · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
              · rcases m.htr 1 2 4 (by decide) (by decide) with h503 | h503
                · linarith only [h261, h262, h501, h503, hc12, hlam, hphi, ht01, u0ehi9]
                · linarith only [h0, h503, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h502, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h501, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h261, h498, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h509 | h509
      · rcases m.htr 0 2 5 (by decide) (by decide) with h510 | h510
        · rcases m.htr 0 3 4 (by decide) (by decide) with h511 | h511
          · rcases m.htr 0 3 5 (by decide) (by decide) with h512 | h512
            · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
              · linarith only [h0, h261, h513, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h513, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h261, h512, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo3]
          · linarith only [h261, h509, h511, hlam]
        · linarith only [h0, h510, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h519 | h519
        · rcases m.htr 0 3 4 (by decide) (by decide) with h520 | h520
          · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
            · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
              · linarith only [h0, h261, h522, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h522, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h509, h520, h521, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h526 | h526
            · rcases m.htr 1 2 3 (by decide) (by decide) with h527 | h527
              · linarith only [h0, h261, h527, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h527, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h526, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7, u5elo3]
        · linarith only [h0, h519, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]

end R2N4
