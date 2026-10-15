import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
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
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h2, h9, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h13, h2, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h16, h2, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h20 | h20
        · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · linarith only [h2, h23, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h2, h25, h28, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h2, h21, h28, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                      · linarith only [h2, h20, h22, h25, h27, h31, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h2, h20, h21, h31, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h2, h20, h26, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                        · linarith only [h25, h35, h38, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
                        · linarith only [h37, h38, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h2, h20, h21, h37, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h22, h25, h35, h36, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h2, h20, h35, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
              · linarith only [h2, h20, h21, h44, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h0, h2, h21, h22, h46, h48, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                      · linarith only [h0, h2, h46, h50, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h2, h20, h21, h50, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h2, h20, h47, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h1, h22, h55, hlam]
                    · linarith only [h46, h54, h55, hlam]
                  · linarith only [h2, h20, h54, hc12, hlam, hphi, u2elo2]
          · linarith only [h2, h20, h21, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
          · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
            · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
              · linarith only [h2, h62, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h0, h20, h65, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h64, h65, h67, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                      · linarith only [h0, h2, h64, h69, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h2, h60, h69, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
                  · linarith only [h0, h20, h72, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                            · rcases h5bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h2, h60, h72, hc12, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1, u0elo4, u2elo2, u3ehi4]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h20, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h20, h75, h77, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u2elo2, u3ehi4]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h20, h75, h77, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo2]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h1, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h72, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p79_1, u3ehi4]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p79_1, u0elo0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h75, h77, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo2]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h75, h77, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo2]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h75, h77, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p79_1, u2elo2, u3ehi4]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h75, h77, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo2]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h60, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h60, h72, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u0elo2]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h76, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h2, h60, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p79_1, u2elo2]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h61, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h74, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h77, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [h78, hlam, p79_0]
                              · have p79_0 := h79c.1
                                have p79_1 := h79c.2.1
                                have p79_2 := h79c.2.2.1
                                have p79_3 := h79c.2.2.2
                                linarith only [hlam, p79_0]
                            · linarith only [h61, h78, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h1, h64, h74, h77, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h2, h60, h76, hlam]
                      · linarith only [h2, h60, h75, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h111, h64, h74, hc12, hlam, hphi, u2elo3]
                          · linarith only [h111, h20, h61, h64, hc12, hlam, hphi, u2elo4]
                        · linarith only [h109, h110, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h109, h2, h60, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
              · linarith only [h0, h116, h2, h60, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
                  · linarith only [h0, h119, h20, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                    · linarith only [h0, h118, h121, h2, h61, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                      · linarith only [h0, h118, h123, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h123, h2, h60, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                  · linarith only [h0, h126, h20, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h128 | h128
                    · linarith only [h1, h128, h61, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                          · linarith only [h118, h128, h132, hc12, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                            · linarith only [h118, h130, h132, h134, hc12, hlam, hphi, u2elo2]
                            · rcases h5bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h118, h128, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p136_1, u0elo4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h20, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h134, hlam, hphi, ht0b, ht34, ht45, ht5b, p136_1, u0elo4, u3ehi3]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h61, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h126, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h134, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p136_1, u3ehi3]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h128, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h131, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p136_1, u2elo2]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h131, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p136_1, u2elo2]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h131, h134, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p136_1, u2elo2, u3ehi3]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h132, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h60, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h118, h128, h60, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p136_1, u0elo4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h131, hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h134, hlam, p136_1]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h1, h118, h128, h2, h60, hc12, hc45, hlam, hphi, ht34, p136_1, u2elo2, u3ehi4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h118, h128, h2, h60, hc12, hc45, hlam, hphi, ht34, p136_1, u2elo2, u3ehi4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [h0, h2, h20, h60, hc12, hc45, hlam, hphi, ht34, p136_1, u2elo2, u3ehi4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hc45, hlam, hphi, ht34, p136_1, u3ehi4]
                              · have p136_0 := h136c.1
                                have p136_1 := h136c.2.1
                                have p136_2 := h136c.2.2.1
                                have p136_3 := h136c.2.2.2
                                linarith only [hlam, p136_0]
                        · linarith only [h131, h2, h60, hlam]
                      · linarith only [h130, h2, h60, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
            · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
              · linarith only [h0, h165, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
                  · linarith only [h0, h168, h20, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                    · linarith only [h167, h168, h170, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                      · linarith only [h0, h167, h172, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                      · linarith only [h0, h167, h172, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                  · linarith only [h0, h175, h20, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h179, h60, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                        · linarith only [h178, h179, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                        · linarith only [h178, h182, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                            · rcases h5bigk with h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h184, h20, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo3]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h20, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h60, hlam, p186_1]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h184, h20, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo3]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h1, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h175, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h177, h182, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p186_1]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p186_1, u0elo4]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h184, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo3]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h184, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo3]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h182, hlam, p186_1]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h184, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p186_1, u2elo3]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h185, h60, hc34, hlam, hphi, p186_1, u3ehi0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h175, h185, hc12, hc34, hlam, hphi, ht23, p186_1]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h185, h20, hc02, hc34, hlam, hphi, ht23, p186_1]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                rcases p186_3 (m.d 0 5) (by simp) with h206 | h206
                                · linarith only [h206, h60, hlam]
                                · linarith only [h164, h206, hlam]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h164, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h177, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h184, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [h185, hlam, p186_0]
                              · have p186_0 := h186c.1
                                have p186_1 := h186c.2.1
                                have p186_2 := h186c.2.2.1
                                have p186_3 := h186c.2.2.2
                                linarith only [hlam, p186_0]
                            · linarith only [h164, h185, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h167, h177, h184, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h217 | h217
                        · linarith only [h217, h60, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                        · linarith only [h216, h217, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h220 | h220
                        · linarith only [h216, h220, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h222 | h222
                          · linarith only [h167, h177, h222, hc12, hlam, hphi, u2elo3]
                          · linarith only [h164, h167, h20, h222, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
              · linarith only [h0, h225, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
                · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                  · linarith only [h0, h20, h228, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
                    · linarith only [h0, h164, h20, h227, h230, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                      · linarith only [h0, h20, h227, h232, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                      · linarith only [h0, h2, h227, h232, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                  · linarith only [h0, h20, h235, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h237 | h237
                    · linarith only [h1, h164, h237, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                        · linarith only [h240, h60, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                        · linarith only [h239, h240, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h243 | h243
                        · linarith only [h239, h243, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                          · linarith only [h227, h237, h245, hc12, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                            · linarith only [h239, h245, h247, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h0, h2, h239, h247, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h250 | h250
      · rcases m.htr 0 2 5 (by decide) (by decide) with h251 | h251
        · linarith only [h0, h1, h251, hlam]
        · linarith only [h250, h251, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h254 | h254
        · linarith only [h0, h1, h254, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h256 | h256
          · rcases m.htr 0 4 5 (by decide) (by decide) with h257 | h257
            · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
              · linarith only [h250, h258, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
                · rcases m.htr 1 2 5 (by decide) (by decide) with h261 | h261
                  · linarith only [h0, h250, h254, h256, h261, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u2elo2, u3ehi4]
                  · linarith only [h0, h1, h260, h261, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                  · linarith only [h0, h254, h264, hlam]
                  · linarith only [h0, h1, h264, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h267 | h267
              · linarith only [h0, h250, h256, h267, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
                  · linarith only [h0, h254, h270, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h269, h270, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h273 | h273
                  · linarith only [h0, h254, h273, hlam]
                  · linarith only [h0, h1, h273, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
            · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
              · linarith only [h0, h277, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                  · linarith only [h0, h1, h254, h280, hlam]
                  · linarith only [h0, h1, h280, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h283 | h283
                  · linarith only [h0, h1, h254, h283, hlam]
                  · linarith only [h0, h1, h283, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
              · linarith only [h0, h250, h286, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h0, h1, h250, h254, h289, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h0, h1, h289, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h292 | h292
                  · linarith only [h0, h254, h292, hlam]
                  · linarith only [h0, h1, h292, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h295 | h295
    · rcases m.htr 0 2 3 (by decide) (by decide) with h296 | h296
      · rcases m.htr 0 2 5 (by decide) (by decide) with h297 | h297
        · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
          · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
            · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
              · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
                · rcases m.htr 1 2 5 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
                      · linarith only [h0, h296, h304, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h306 | h306
                        · linarith only [h0, h296, h306, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                        · linarith only [h298, h306, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                      · linarith only [h296, h309, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h299, h301, h303, h309, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h0, h302, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h296, h298, h301, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
              · linarith only [h0, h296, h298, h300, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
              · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                    · linarith only [h0, h295, h298, h299, h318, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                      · linarith only [h296, h320, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h0, h295, h316, h318, h320, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h0, h317, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h295, h298, h316, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
              · linarith only [h0, h295, h298, h315, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
            · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
              · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
                      · linarith only [h296, h298, h331, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
                        · linarith only [h0, h295, h296, h298, h333, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                        · linarith only [h0, h295, h329, h333, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                      · linarith only [h0, h296, h336, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h0, h295, h326, h328, h330, h336, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h0, h329, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h328, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h295, h296, h298, h327, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
              · rcases m.htr 1 2 4 (by decide) (by decide) with h343 | h343
                · rcases m.htr 1 2 5 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h345 | h345
                    · linarith only [h0, h295, h296, h298, h326, h345, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                      · linarith only [h296, h298, h347, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h295, h343, h345, h347, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h0, h344, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h343, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h295, h296, h298, h342, hlam]
        · linarith only [h296, h297, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
        · rcases m.htr 0 3 5 (by decide) (by decide) with h355 | h355
          · rcases m.htr 0 4 5 (by decide) (by decide) with h356 | h356
            · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
              · linarith only [h296, h357, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h295, h355, h357, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
              · linarith only [h0, h295, h296, h355, h360, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
              · linarith only [h0, h295, h355, h360, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
          · linarith only [h0, h295, h296, h355, hlam]
        · linarith only [h0, h295, h354, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h365 | h365
      · rcases m.htr 0 2 5 (by decide) (by decide) with h366 | h366
        · rcases m.htr 0 3 5 (by decide) (by decide) with h367 | h367
          · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
            · rcases m.htr 1 2 3 (by decide) (by decide) with h369 | h369
              · rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
                · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h372 | h372
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                      · linarith only [h365, h373, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h365, h375, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                        · linarith only [h367, h375, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · linarith only [h295, h368, h372, hlam]
                  · linarith only [h0, h366, h371, hlam]
                · linarith only [h0, h365, h367, h370, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
              · linarith only [h0, h365, h367, h369, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
              · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                · rcases m.htr 1 2 5 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                      · linarith only [h365, h386, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                        · linarith only [h0, h365, h388, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                        · linarith only [h367, h388, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                      · linarith only [h0, h365, h391, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h393 | h393
                        · linarith only [h391, h393, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h365, h367, h393, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h0, h384, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h365, h367, h383, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
              · linarith only [h0, h365, h367, h382, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
            · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
              · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                      · linarith only [h365, h404, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                        · linarith only [h365, h367, h406, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
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
                                linarith only [h295, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hc25, hlam, hphi, ht0b, ht5b, p410_1, u0elo4]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h367, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hc45, hlam, hphi, ht0b, ht5b, p410_1, u0elo4]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h295, h403, hc01, hc14, hlam, hphi, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h401, h403, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h401, h403, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h401, h403, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h366, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h402, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h406, hlam, p410_1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h0, h366, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo1]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h365, h367, hc35, hlam, hphi, p410_1, u3ehi2]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h0, h295, h366, h406, h409, hc01, hc34, hlam, hphi, ht12, p410_1, u2elo1, u3ehi2]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h406, h409, hc34, hlam, hphi, p410_1, u3ehi2]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                rcases p410_3 (m.d 0 5) (by simp) with h430 | h430
                                · linarith only [h367, h430, hlam]
                                · linarith only [h399, h430, hlam]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h399, hlam, p410_0]
                              · have p410_0 := h410c.1
                                have p410_1 := h410c.2.1
                                have p410_2 := h410c.2.2.1
                                have p410_3 := h410c.2.2.2
                                linarith only [h403, hlam, p410_0]
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
                            · linarith only [h399, h409, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h401, h403, h404, h408, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · linarith only [h295, h399, h403, hlam]
                  · linarith only [h0, h366, h402, hlam]
                · linarith only [h0, h401, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h365, h400, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
              · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                      · linarith only [h365, h448, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h450 | h450
                        · linarith only [h365, h367, h399, h445, h447, h450, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                          · linarith only [h367, h399, h445, h452, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                          · linarith only [h445, h447, h448, h452, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                      · linarith only [h365, h367, h455, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                        · linarith only [h0, h365, h367, h457, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                          · linarith only [h367, h399, h445, h459, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h445, h447, h455, h461, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h455, h461, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h446, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h365, h445, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h0, h365, h444, hlam]
        · linarith only [h365, h366, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h468 | h468
        · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
          · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
            · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
              · linarith only [h365, h471, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h471, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
              · linarith only [h365, h468, h469, h474, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
              · linarith only [h0, h474, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h365, h468, h469, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h478 | h478
          · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
            · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
              · linarith only [h365, h480, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h480, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
              · linarith only [h0, h365, h483, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h483, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h486 | h486
            · rcases m.htr 1 2 3 (by decide) (by decide) with h487 | h487
              · linarith only [h0, h365, h487, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h487, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
              · linarith only [h0, h365, h490, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h490, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_10_12_13_25_L_I_L_0_L_0_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
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
  have u5elo0 := h5elo (m.d 0 5) (by simp)
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
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                                · linarith only [h12, h15, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h15, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h14, h8, hc24, hlam, hphi, ht45, u5elo0]
                            · linarith only [h13, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h12, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h10, h6, hc13, hlam, hphi, u3elo0]
                    · linarith only [h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h8, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h7, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                      · linarith only [h26, h29, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                          · linarith only [h1, h31, h32, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                                · rcases h0bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h32, h34, h36, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h40 | h40
                                    · rcases p37_3 (m.d 0 2) (by simp) with h41 | h41
                                      · linarith only [h0, h41, hlam]
                                      · linarith only [h4, h41, hlam]
                                    · linarith only [h1, h40, hlam]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h45 | h45
                                    · rcases p37_3 (m.d 0 2) (by simp) with h46 | h46
                                      · linarith only [h0, h46, hlam]
                                      · linarith only [h46, h5, hlam]
                                    · linarith only [h2, h45, hlam]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h50 | h50
                                    · rcases p37_3 (m.d 0 2) (by simp) with h51 | h51
                                      · linarith only [h0, h51, hlam]
                                      · linarith only [h32, h34, h36, h5, h51, hc45, hlam, hphi, u5elo0]
                                    · linarith only [h3, h50, hlam]
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
                                    linarith only [h1, h31, h36, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p37_1, u2elo0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h1, h31, h36, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p37_1, u2elo0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h59 | h59
                                    · rcases p37_3 (m.d 0 2) (by simp) with h60 | h60
                                      · rcases p37_3 (m.d 0 3) (by simp) with h61 | h61
                                        · linarith only [h4, h61, hlam]
                                        · linarith only [h26, h61, hlam]
                                      · linarith only [h60, hlam, p37_0]
                                    · linarith only [h3, h59, hlam]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h1, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h4, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h6, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h3, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p37_1, u3elo3]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h2, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h5, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h6, hc03, hlam, hphi, p37_1, u3elo3]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    rcases p37_3 (m.d 0 1) (by simp) with h75 | h75
                                    · rcases p37_3 (m.d 0 2) (by simp) with h76 | h76
                                      · rcases p37_3 (m.d 0 3) (by simp) with h77 | h77
                                        · linarith only [h6, h77, hlam]
                                        · linarith only [h26, h77, hlam]
                                      · linarith only [h0, h28, h34, h36, h76, hc45, hlam, hphi, u5elo0]
                                    · linarith only [h3, h75, hlam]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h3, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p37_1, u5elo0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h26, hlam, p37_0]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [h27, hlam, p37_1]
                                  · have p37_0 := h37c.1
                                    have p37_1 := h37c.2.1
                                    have p37_2 := h37c.2.2.1
                                    have p37_3 := h37c.2.2.2
                                    linarith only [hlam, p37_0]
                                · linarith only [h34, h36, h4, h6, hc35, hlam, hphi, u5elo4]
                              · linarith only [h27, h35, hc24, hlam, hphi, ht45, u5elo0]
                            · linarith only [h34, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h26, h31, h6, hc13, hlam, hphi, u3elo3]
                    · linarith only [h28, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h27, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h26, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h94 | h94
              · linarith only [h4, h5, h94, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
                · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                      · linarith only [h94, h99, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                          · linarith only [h1, h101, h102, h94, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · linarith only [h102, h4, h5, hc23, hlam, hphi, u3elo3]
                        · linarith only [h101, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h98, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h4, h5, h97, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h96, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h109 | h109
            · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
              · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 4 5 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                              · linarith only [h109, h118, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h116, h118, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h109, h116, h117, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h109, h114, h116, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h111, h114, h115, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · linarith only [h110, h114, h4, hc13, hlam, hphi, u3elo2]
                    · linarith only [h113, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h112, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h111, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h109, h110, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h129 | h129
              · rcases m.htr 0 3 5 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
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
                                    rcases p139_3 (m.d 0 1) (by simp) with h141 | h141
                                    · rcases p139_3 (m.d 0 2) (by simp) with h142 | h142
                                      · linarith only [h0, h142, hlam]
                                      · rcases p139_3 (m.d 0 3) (by simp) with h144 | h144
                                        · linarith only [h1, h144, hlam]
                                        · linarith only [h144, h4, hlam]
                                    · linarith only [h0, h141, hlam]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h1, h133, h138, hc01, hc45, hlam, hphi, ht0b, ht5b, p139_1]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    rcases p139_3 (m.d 0 1) (by simp) with h149 | h149
                                    · rcases p139_3 (m.d 0 2) (by simp) with h150 | h150
                                      · linarith only [h0, h150, hlam]
                                      · rcases p139_3 (m.d 0 3) (by simp) with h152 | h152
                                        · linarith only [h1, h152, hlam]
                                        · linarith only [h129, h152, hlam]
                                    · linarith only [h149, h2, hlam]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    rcases p139_3 (m.d 0 1) (by simp) with h156 | h156
                                    · rcases p139_3 (m.d 0 2) (by simp) with h157 | h157
                                      · linarith only [h0, h157, hlam]
                                      · linarith only [h0, h132, h136, h138, h157, hc45, hlam, hphi, u5elo0]
                                    · linarith only [h156, h3, hlam]
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
                                    linarith only [h109, hlam, p139_1]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h109, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p139_1, u2elo3]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h1, hlam, p139_1]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [hc02, hlam, hphi, ht23, p139_1, u3elo0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [hlam, p139_0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h0, h109, h132, h136, h138, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p139_1, u3elo2]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    rcases p139_3 (m.d 0 1) (by simp) with h170 | h170
                                    · rcases p139_3 (m.d 0 2) (by simp) with h171 | h171
                                      · linarith only [h171, h4, hlam]
                                      · linarith only [h0, h132, h136, h138, h171, hc45, hlam, hphi, u5elo0]
                                    · linarith only [h170, h3, hlam]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h2, hlam, p139_0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h0, h109, h132, h135, h136, h138, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p139_1, u3elo2]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h129, hlam, p139_0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [hlam, p139_0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    rcases p139_3 (m.d 0 1) (by simp) with h179 | h179
                                    · rcases p139_3 (m.d 0 2) (by simp) with h180 | h180
                                      · linarith only [h109, h180, hlam]
                                      · linarith only [h0, h109, h132, h135, h136, h138, h180, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p139_1, u3elo2]
                                    · linarith only [h179, h3, hlam]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h3, hlam, p139_0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h0, h132, h136, h138, hc45, hlam, hphi, p139_1, u5elo0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h130, hlam, p139_0]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [h131, hlam, p139_1]
                                  · have p139_0 := h139c.1
                                    have p139_1 := h139c.2.1
                                    have p139_2 := h139c.2.2.1
                                    have p139_3 := h139c.2.2.2
                                    linarith only [hlam, p139_0]
                                · linarith only [h138, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h109, h131, h137, hc04, hlam, hphi, ht45, u5elo0]
                            · linarith only [h136, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h132, h133, h135, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h130, h133, h134, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · linarith only [h129, h133, h4, hc13, hlam, hphi, u3elo2]
                    · linarith only [h132, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h131, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h130, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 0 4 5 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                      · linarith only [h0, h129, h200, h201, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h203 | h203
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                          · linarith only [h0, h129, h200, h204, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h0, h200, h204, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h203, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h200, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h129, h199, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h198, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
          · rcases m.htr 0 2 4 (by decide) (by decide) with h214 | h214
            · linarith only [h0, h2, h214, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h216 | h216
              · linarith only [h1, h2, h216, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
                · rcases m.htr 0 4 5 (by decide) (by decide) with h219 | h219
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                      · linarith only [h216, h221, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h2, h220, h221, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h220, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h2, h219, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h218, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h227 | h227
            · linarith only [h0, h2, h213, h227, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h229 | h229
              · linarith only [h1, h2, h229, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
                · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                      · linarith only [h213, h229, h234, hc02, hlam, hphi, ht23, u3elo1]
                      · linarith only [h0, h2, h233, h234, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h233, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h2, h232, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h231, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h0, h212, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h242 | h242
    · rcases m.htr 0 1 4 (by decide) (by decide) with h243 | h243
      · rcases m.htr 0 1 5 (by decide) (by decide) with h244 | h244
        · rcases m.htr 0 2 3 (by decide) (by decide) with h245 | h245
          · rcases m.htr 0 2 4 (by decide) (by decide) with h246 | h246
            · rcases m.htr 0 3 4 (by decide) (by decide) with h247 | h247
              · rcases m.htr 0 3 5 (by decide) (by decide) with h248 | h248
                · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
                      · linarith only [h0, h242, h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h247, h251, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h250, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h249, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h247, h248, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h257 | h257
                · rcases m.htr 0 4 5 (by decide) (by decide) with h258 | h258
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                      · linarith only [h247, h260, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h0, h243, h260, h262, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h247, h257, h262, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h259, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h247, h257, h258, hc35, hlam, hphi, u5elo4]
                · linarith only [h257, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h0, h243, h246, hlam]
          · linarith only [h0, h242, h245, hc13, hlam, hphi, u3elo2]
        · linarith only [h242, h244, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h271 | h271
        · rcases m.htr 0 2 3 (by decide) (by decide) with h272 | h272
          · rcases m.htr 0 2 4 (by decide) (by decide) with h273 | h273
            · rcases m.htr 0 3 4 (by decide) (by decide) with h274 | h274
              · linarith only [h242, h243, h274, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h276 | h276
                · rcases m.htr 0 4 5 (by decide) (by decide) with h277 | h277
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h278 | h278
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
                      · linarith only [h0, h242, h274, h279, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h242, h243, h279, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h278, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h277, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h276, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
              · linarith only [h0, h242, h273, h285, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h287 | h287
                · rcases m.htr 0 4 5 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                      · linarith only [h285, h290, hc03, hlam, hphi, u3elo1]
                      · linarith only [h242, h243, h290, hc13, hlam, hphi, u3elo3]
                    · linarith only [h289, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h242, h273, h288, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h287, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h242, h272, hc13, hlam, hphi, u3elo2]
        · linarith only [h242, h271, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h298 | h298
      · rcases m.htr 0 1 5 (by decide) (by decide) with h299 | h299
        · rcases m.htr 0 2 3 (by decide) (by decide) with h300 | h300
          · rcases m.htr 0 2 4 (by decide) (by decide) with h301 | h301
            · rcases m.htr 0 3 4 (by decide) (by decide) with h302 | h302
              · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
                · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                                · linarith only [h242, h298, h306, h311, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · linarith only [h311, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h242, h298, h304, h310, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h309, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h242, h298, h306, h308, hc23, hlam, hphi, u3elo1]
                        · linarith only [h242, h298, h306, h307, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h242, h306, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h305, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h304, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h303, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h242, h298, h302, hlam]
            · linarith only [h242, h298, h300, h301, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h324 | h324
            · rcases m.htr 0 3 4 (by decide) (by decide) with h325 | h325
              · rcases m.htr 0 3 5 (by decide) (by decide) with h326 | h326
                · rcases m.htr 0 4 5 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h332 | h332
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h333 | h333
                              · linarith only [h300, h324, h333, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h333, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h300, h332, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h298, h300, h329, h331, hlam]
                        · linarith only [h242, h298, h329, h330, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h242, h298, h329, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h298, h328, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h327, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h326, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h298, h300, h325, hlam]
            · linarith only [h0, h298, h324, hlam]
        · linarith only [h298, h299, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h346 | h346
        · rcases m.htr 0 2 3 (by decide) (by decide) with h347 | h347
          · rcases m.htr 0 2 4 (by decide) (by decide) with h348 | h348
            · rcases m.htr 0 3 4 (by decide) (by decide) with h349 | h349
              · rcases m.htr 0 3 5 (by decide) (by decide) with h350 | h350
                · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h356 | h356
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                                · linarith only [h0, h347, h355, h358, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · linarith only [h358, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h357, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h356, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h242, h349, h355, hc23, hlam, hphi, u3elo1]
                        · linarith only [h298, h353, h354, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h242, h349, h353, hlam]
                    · linarith only [h0, h352, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h351, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h350, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
                · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                      · linarith only [h242, h346, h349, h371, h372, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h242, h346, h371, h372, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h0, h371, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h242, h346, h349, h370, hc15, hlam, hphi, u5elo4]
                · linarith only [h242, h346, h369, hc15, hlam, hphi, u5elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h378 | h378
              · linarith only [h347, h348, h378, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h380 | h380
                · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h382 | h382
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                      · linarith only [h378, h383, hc03, hlam, hphi, u3elo1]
                      · linarith only [h242, h346, h382, h383, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h0, h382, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h347, h348, h381, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h242, h346, h380, hc15, hlam, hphi, u5elo3]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h389 | h389
            · rcases m.htr 0 3 4 (by decide) (by decide) with h390 | h390
              · rcases m.htr 0 3 5 (by decide) (by decide) with h391 | h391
                · rcases m.htr 0 4 5 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h395 | h395
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                              · linarith only [h347, h389, h398, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · linarith only [h396, h398, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h298, h346, h347, h389, h393, h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h298, h346, h347, h389, h393, h396, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h298, h346, h393, h394, h395, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h390, h394, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h393, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h298, h346, h392, hc15, hlam, hphi, u5elo4]
                · linarith only [h391, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h347, h389, h390, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h409 | h409
              · rcases m.htr 0 3 5 (by decide) (by decide) with h410 | h410
                · rcases m.htr 0 4 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h412 | h412
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h413 | h413
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                                · rcases h0bigk with h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h0, hlam, p419_1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h242, hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h298, hlam, p419_1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p419_1, u2elo1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h389, h415, hc01, hlam, hphi, ht12, ht23, p419_1, u3elo2]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h347, hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h389, hlam, p419_1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h346, h389, h412, h415, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p419_1, u3elo2]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h242, h346, h412, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p419_1, u3elo1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h242, hc02, hlam, hphi, ht23, p419_1, u3elo1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h0, h242, h346, h389, h412, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p419_1, u3elo1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    rcases p419_3 (m.d 0 1) (by simp) with h434 | h434
                                    · linarith only [h242, h434, hlam]
                                    · linarith only [h346, h434, hlam]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h346, h389, h412, h415, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p419_1, u3elo2]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h0, h346, h389, h412, h415, h416, h418, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p419_1, u3elo2]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h409, hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    rcases p419_3 (m.d 0 1) (by simp) with h441 | h441
                                    · linarith only [h298, h441, hlam]
                                    · linarith only [h346, h441, hlam]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h346, hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h0, h346, h412, h416, h418, hc45, hlam, hphi, p419_1, u5elo0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h410, hlam, p419_0]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [h411, hlam, p419_1]
                                  · have p419_0 := h419c.1
                                    have p419_1 := h419c.2.1
                                    have p419_2 := h419c.2.2.1
                                    have p419_3 := h419c.2.2.2
                                    linarith only [hlam, p419_0]
                                · linarith only [h418, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h389, h411, h417, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                            · linarith only [h347, h416, hc03, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h346, h347, h412, h415, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h298, h346, h412, h413, h414, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h409, h413, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h412, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h411, hc04, hlam, hphi, ht45, u5elo4]
                · linarith only [h410, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h458 | h458
                · rcases m.htr 0 4 5 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                      · linarith only [h0, h346, h347, h409, h460, h461, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h242, h346, h460, h461, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h0, h460, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h346, h347, h409, h459, hc15, hlam, hphi, u5elo4]
                · linarith only [h0, h346, h347, h458, hc15, hlam, hphi, u5elo3]
        · linarith only [h346, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
