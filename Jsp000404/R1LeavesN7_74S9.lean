import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
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
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h10, h14, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h14, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                              · linarith only [h17, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h17, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                          · linarith only [h12, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                        · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                            · linarith only [h2, h26, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                              · linarith only [h28, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h28, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                          · linarith only [h25, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                        · linarith only [h24, h5, hc12, hlam, hphi, u2elo0]
                      · linarith only [h23, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h35, h7, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                          · linarith only [h1, h35, h40, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                              · linarith only [h38, h43, h7, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                                · linarith only [h1, h35, h38, h45, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                                    · rcases h0bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h0, h39, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h38, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h47, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h35, h38, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h0, hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h38, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p49_1, u2elo0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h35, h38, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p49_1, u2elo0, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, hlam, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h4, hlam, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h7, hlam, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h35, hlam, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h2, hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h5, hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h38, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h35, h38, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p49_1, u2elo0, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h3, hlam, p49_0]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h6, hlam, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h1, h38, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1, u3ehi2]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [h37, hlam, p49_1]
                                      · have p49_0 := h49c.1
                                        have p49_1 := h49c.2.1
                                        have p49_2 := h49c.2.2.1
                                        have p49_3 := h49c.2.2.2
                                        linarith only [hlam, p49_0]
                                    · linarith only [h1, h38, h48, h7, hc45, hlam, hphi, ht34, u3ehi2]
                                  · linarith only [h2, h42, h43, h47, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                              · linarith only [h37, h38, h42, h7, h77, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h37, h39, h42, h5, h77, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                        · linarith only [h38, h39, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
                      · linarith only [h38, h4, hc12, hlam, hphi, u2elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h1, h37, h7, h84, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                            · linarith only [h2, h37, h7, h86, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                              · linarith only [h82, h88, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                · linarith only [h1, h7, h82, h90, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                  · linarith only [h0, h37, h7, h83, h92, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                                    · linarith only [h1, h37, h7, h82, h94, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h1, h7, h82, h94, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h5, h83, hc12, hlam, hphi, u2elo0]
                      · linarith only [h4, h82, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h101 | h101
            · rcases m.htr 0 2 5 (by decide) (by decide) with h102 | h102
              · rcases m.htr 0 3 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                      · linarith only [h106, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                              · linarith only [h101, h111, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                              · linarith only [h1, h109, h111, h4, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h101, h105, h110, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · linarith only [h104, h109, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · linarith only [h101, h108, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                      · linarith only [h117, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h103, h105, h121, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                              · linarith only [h101, h123, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                              · linarith only [h0, h103, h105, h119, h123, h4, hc24, hc45, hlam, hphi]
                          · linarith only [h104, h120, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · linarith only [h101, h119, h4, hc12, hlam, hphi, u2elo2]
                  · linarith only [h103, h104, hc35, hlam, hphi, u3ehi3]
                · linarith only [h101, h103, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
                    · linarith only [h101, h102, h132, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
                      · linarith only [h134, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h130, h132, h138, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                              · linarith only [h101, h140, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                              · linarith only [h130, h132, h140, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h131, h137, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · linarith only [h101, h136, h4, hc12, hlam, hphi, u2elo2]
                  · linarith only [h130, h131, hc35, hlam, hphi, u3ehi3]
                · linarith only [h101, h130, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h147 | h147
              · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
                · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
                      · linarith only [h151, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                        · linarith only [h0, h101, h153, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                · linarith only [h101, h147, h158, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
                                · linarith only [h101, h147, h155, h157, h158, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h147, h155, h157, h3, h4, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h101, h150, h153, h156, hc12, hlam, hphi, u2elo3]
                          · linarith only [h149, h155, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · linarith only [h101, h147, h150, hlam]
                  · linarith only [h148, h149, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
                  · linarith only [h148, h166, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h147, h166, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
                · rcases m.htr 0 3 5 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
                      · linarith only [h172, h4, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                        · linarith only [h0, h101, h174, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h177 | h177
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                                    · rcases h0bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        rcases p182_3 (m.d 0 1) (by simp) with h184 | h184
                                        · rcases p182_3 (m.d 0 2) (by simp) with h185 | h185
                                          · linarith only [h0, h185, hlam]
                                          · rcases p182_3 (m.d 0 3) (by simp) with h187 | h187
                                            · linarith only [h1, h187, hlam]
                                            · linarith only [h187, h4, hlam]
                                        · linarith only [h0, h184, hlam]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h1, h176, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1, u3ehi4]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h176, h177, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1, u3ehi4]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h176, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1, u3ehi4]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h0, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h4, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h101, hlam, p182_1]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h147, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h1, hlam, p182_1]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h0, h4, hc12, hlam, hphi, p182_1, u2elo2]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h176, h177, h2, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p182_1, u2elo2, u3ehi4]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h176, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p182_1, u2elo2, u3ehi4]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h2, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h0, h101, h178, hc12, hlam, hphi, p182_1, u2elo2]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h169, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h101, h176, h178, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p182_1, u2elo2, u3ehi4]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h3, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h0, h147, h178, h180, hc12, hlam, hphi, p182_1, u2elo2]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h170, hlam, p182_0]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [h171, hlam, p182_1]
                                      · have p182_0 := h182c.1
                                        have p182_1 := h182c.2.1
                                        have p182_2 := h182c.2.2.1
                                        have p182_3 := h182c.2.2.2
                                        linarith only [hlam, p182_0]
                                    · linarith only [h177, h181, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h101, h177, h180, h2, hlam]
                                · linarith only [h1, h176, h179, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · linarith only [h1, h176, h178, h4, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h101, h171, h174, h177, hc12, hlam, hphi, u2elo3]
                          · linarith only [h170, h176, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                      · linarith only [h0, h169, h220, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                        · linarith only [h0, h101, h222, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                            · linarith only [h171, h2, h225, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h229 | h229
                                  · linarith only [h101, h171, h227, h229, hc02, hlam, hphi, u2elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                                    · linarith only [h0, h101, h229, h231, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h0bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        rcases p233_3 (m.d 0 1) (by simp) with h235 | h235
                                        · rcases p233_3 (m.d 0 2) (by simp) with h236 | h236
                                          · linarith only [h0, h236, hlam]
                                          · rcases p233_3 (m.d 0 3) (by simp) with h238 | h238
                                            · linarith only [h1, h238, hlam]
                                            · linarith only [h238, h4, hlam]
                                        · linarith only [h0, h235, hlam]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h1, h224, h231, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1, u3ehi3]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h169, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1, u3ehi3]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h169, h171, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p233_1, u3ehi3]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h4, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h101, hlam, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h147, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h1, hlam, p233_1]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, h4, hc12, hlam, hphi, p233_1, u2elo2]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p233_1, u2elo2]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, h147, h4, hc12, hlam, hphi, p233_1, u2elo2]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h2, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, h1, h101, h224, h229, h231, h4, hc12, hc45, hlam, hphi, ht34, p233_1, u2elo2, u3ehi3]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h169, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h171, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h3, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h0, h147, h228, hc12, hlam, hphi, p233_1, u2elo2]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h170, hlam, p233_0]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [h147, h228, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p233_1, u2elo2]
                                      · have p233_0 := h233c.1
                                        have p233_1 := h233c.2.1
                                        have p233_2 := h233c.2.2.1
                                        have p233_3 := h233c.2.2.2
                                        linarith only [hlam, p233_0]
                                · linarith only [h1, h224, h228, h4, hlam]
                              · linarith only [h1, h224, h227, h4, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h170, h224, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                  · linarith only [h169, h170, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                  · linarith only [h169, h269, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h271 | h271
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
                      · linarith only [h0, h272, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h274 | h274
                        · linarith only [h0, h101, h271, h274, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                          · linarith only [h1, h269, h276, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                              · linarith only [h169, h279, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                                · linarith only [h1, h269, h279, h281, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h283 | h283
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                                    · rcases h0bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        rcases p285_3 (m.d 0 1) (by simp) with h287 | h287
                                        · rcases p285_3 (m.d 0 2) (by simp) with h288 | h288
                                          · linarith only [h0, h288, hlam]
                                          · rcases p285_3 (m.d 0 3) (by simp) with h290 | h290
                                            · linarith only [h1, h290, hlam]
                                            · linarith only [h290, h4, hlam]
                                        · linarith only [h0, h287, hlam]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1, u3ehi1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h2, h276, h278, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1, u3ehi1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h276, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1, u3ehi1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h0, hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h4, hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h101, hlam, p285_1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h147, hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h1, hlam, p285_1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h0, h281, h4, hc12, hc35, hlam, hphi, ht23, p285_1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h169, hlam, p285_1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h269, hlam, p285_1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h2, hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h0, h101, hc12, hlam, hphi, p285_1, u2elo3]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h101, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u2elo3, u3ehi0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h101, h276, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u2elo3, u3ehi1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h3, hlam, p285_0]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h0, h147, h283, hc12, hlam, hphi, p285_1, u2elo3]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h1, h147, h283, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u2elo3, u3ehi1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [h271, hlam, p285_1]
                                      · have p285_0 := h285c.1
                                        have p285_1 := h285c.2.1
                                        have p285_2 := h285c.2.2.1
                                        have p285_3 := h285c.2.2.2
                                        linarith only [hlam, p285_0]
                                    · linarith only [h1, h169, h284, hc45, hlam, hphi, ht34, u3ehi1]
                                  · linarith only [h101, h2, h278, h283, hlam]
                            · linarith only [h101, h271, h274, h278, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                      · linarith only [h0, h320, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
                        · linarith only [h0, h101, h322, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h324 | h324
                          · linarith only [h1, h169, h324, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h326 | h326
                            · linarith only [h169, h2, h271, h326, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h328 | h328
                              · linarith only [h1, h169, h328, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
                                · linarith only [h1, h269, h328, h330, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
                                  · linarith only [h1, h169, h271, h332, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                                    · linarith only [h328, h332, h334, h4, hc02, hc34, hlam, hphi, ht23]
                                    · linarith only [h1, h169, h334, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h337 | h337
          · rcases m.htr 0 2 4 (by decide) (by decide) with h338 | h338
            · rcases m.htr 0 2 5 (by decide) (by decide) with h339 | h339
              · linarith only [h0, h3, h339, hlam]
              · linarith only [h337, h339, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h337, h338, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h343 | h343
            · rcases m.htr 0 2 5 (by decide) (by decide) with h344 | h344
              · linarith only [h0, h3, h337, h344, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h346 | h346
                · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
                  · linarith only [h1, h3, h347, hlam]
                  · linarith only [h346, h347, hc35, hlam, hphi, u3ehi3]
                · linarith only [h337, h343, h346, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h351 | h351
              · linarith only [h0, h3, h337, h351, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h353 | h353
                · rcases m.htr 0 3 5 (by decide) (by decide) with h354 | h354
                  · linarith only [h1, h3, h354, hlam]
                  · linarith only [h353, h354, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h357 | h357
                  · linarith only [h353, h357, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                    · linarith only [h2, h3, h359, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h361 | h361
                      · linarith only [h337, h361, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h363 | h363
                        · linarith only [h0, h3, h343, h351, h353, h363, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
                          · linarith only [h1, h353, h365, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1, h3, h365, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h368 | h368
        · rcases m.htr 0 2 3 (by decide) (by decide) with h369 | h369
          · rcases m.htr 0 2 4 (by decide) (by decide) with h370 | h370
            · linarith only [h0, h2, h370, hlam]
            · linarith only [h369, h370, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h373 | h373
            · linarith only [h0, h2, h369, h373, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h375 | h375
              · rcases m.htr 0 3 4 (by decide) (by decide) with h376 | h376
                · linarith only [h1, h2, h376, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h378 | h378
                  · linarith only [h376, h378, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h369, h375, h378, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h381 | h381
                · linarith only [h1, h2, h381, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h383 | h383
                  · linarith only [h381, h383, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
                      · linarith only [h369, h386, hc02, hlam, hphi, u2elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h388 | h388
                        · linarith only [h0, h2, h373, h388, hlam]
                        · linarith only [h1, h2, h388, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                    · linarith only [h1, h2, h385, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h392 | h392
          · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
            · linarith only [h0, h2, h393, hlam]
            · linarith only [h392, h393, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h396 | h396
            · linarith only [h0, h2, h396, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h398 | h398
              · linarith only [h1, h368, h392, h398, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
                · linarith only [h1, h2, h400, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h402 | h402
                  · linarith only [h400, h402, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                      · linarith only [h0, h2, h392, h405, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                        · linarith only [h0, h368, h396, h404, h407, hlam]
                        · linarith only [h1, h2, h407, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
                    · linarith only [h1, h2, h404, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h411 | h411
      · rcases m.htr 0 1 5 (by decide) (by decide) with h412 | h412
        · rcases m.htr 0 2 3 (by decide) (by decide) with h413 | h413
          · linarith only [h0, h1, h413, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h415 | h415
            · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
              · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
                · rcases m.htr 0 3 5 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h419 | h419
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
                      · linarith only [h413, h420, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1, h420, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h423 | h423
                      · linarith only [h0, h1, h423, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h423, hc12, hlam, hphi, u2elo2]
                  · linarith only [h417, h418, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h411, h417, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
                · rcases m.htr 0 3 5 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
                    · linarith only [h415, h416, h430, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h432 | h432
                      · linarith only [h0, h1, h432, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h432, hc12, hlam, hphi, u2elo2]
                  · linarith only [h428, h429, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h415, h416, h428, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h437 | h437
              · rcases m.htr 0 3 4 (by decide) (by decide) with h438 | h438
                · rcases m.htr 0 3 5 (by decide) (by decide) with h439 | h439
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                      · linarith only [h0, h1, h413, h441, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1, h441, hc12, hlam, hphi, u2elo2]
                    · linarith only [h415, h437, h440, hlam]
                  · linarith only [h438, h439, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h411, h438, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h447 | h447
                · rcases m.htr 0 3 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                      · linarith only [h0, h1, h450, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h450, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h453 | h453
                      · linarith only [h0, h1, h413, h453, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1, h453, hc12, hlam, hphi, u2elo2]
                  · linarith only [h447, h448, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h411, h447, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h458 | h458
          · linarith only [h0, h1, h458, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h460 | h460
            · rcases m.htr 0 2 5 (by decide) (by decide) with h461 | h461
              · linarith only [h0, h412, h458, h461, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h463 | h463
                · rcases m.htr 0 3 5 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h465 | h465
                    · linarith only [h0, h412, h458, h460, h465, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
                      · linarith only [h0, h1, h458, h467, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h467, hc12, hlam, hphi, u2elo2]
                  · linarith only [h463, h464, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h460, h463, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
              · linarith only [h411, h412, h460, h472, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h474 | h474
                · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h476 | h476
                    · linarith only [h411, h412, h476, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
                      · linarith only [h0, h1, h478, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h478, hc12, hlam, hphi, u2elo2]
                  · linarith only [h474, h475, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h411, h474, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h483 | h483
        · rcases m.htr 0 2 3 (by decide) (by decide) with h484 | h484
          · linarith only [h0, h1, h484, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h486 | h486
            · linarith only [h0, h411, h486, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h488 | h488
              · rcases m.htr 0 3 4 (by decide) (by decide) with h489 | h489
                · rcases m.htr 0 3 5 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                      · linarith only [h0, h1, h484, h492, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h492, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h411, h488, h491, hlam]
                  · linarith only [h489, h490, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h497 | h497
                  · linarith only [h489, h497, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h1, h488, h497, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
                · rcases m.htr 0 3 5 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h502 | h502
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                      · linarith only [h0, h1, h484, h503, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h1, h503, hc12, hlam, hphi, u2elo2]
                    · linarith only [h411, h483, h502, hlam]
                  · linarith only [h500, h501, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
                  · linarith only [h500, h508, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h483, h508, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h511 | h511
          · linarith only [h0, h1, h511, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h513 | h513
            · linarith only [h0, h411, h513, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h515 | h515
              · linarith only [h0, h483, h515, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h517 | h517
                · rcases m.htr 0 3 5 (by decide) (by decide) with h518 | h518
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h519 | h519
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h520 | h520
                      · linarith only [h0, h1, h511, h520, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h520, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
                      · linarith only [h0, h1, h523, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h523, hc12, hlam, hphi, u2elo2]
                  · linarith only [h517, h518, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h527 | h527
                  · linarith only [h517, h527, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h529 | h529
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
                      · linarith only [h0, h1, h530, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1, h530, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                      · linarith only [h0, h1, h511, h533, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h533, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h536 | h536
    · linarith only [h0, h536, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h538 | h538
      · rcases m.htr 0 1 5 (by decide) (by decide) with h539 | h539
        · rcases m.htr 0 2 3 (by decide) (by decide) with h540 | h540
          · rcases m.htr 0 2 4 (by decide) (by decide) with h541 | h541
            · rcases m.htr 0 2 5 (by decide) (by decide) with h542 | h542
              · rcases m.htr 0 3 4 (by decide) (by decide) with h543 | h543
                · rcases m.htr 0 3 5 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h545 | h545
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h548 | h548
                          · linarith only [h536, h539, h546, h548, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                          · linarith only [h536, h543, h548, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h538, h544, h545, h547, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
                      · linarith only [h0, h538, h544, h545, h546, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h554 | h554
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h555 | h555
                          · linarith only [h536, h539, h553, h555, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                          · linarith only [h536, h538, h543, h555, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h536, h539, h543, h545, h553, h554, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                      · linarith only [h0, h539, h543, h545, h553, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h543, h544, hc35, hlam, hphi, u3ehi3]
                · linarith only [h536, h538, h543, hlam]
              · linarith only [h540, h542, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h540, h541, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h564 | h564
            · rcases m.htr 0 2 5 (by decide) (by decide) with h565 | h565
              · rcases m.htr 0 3 4 (by decide) (by decide) with h566 | h566
                · rcases m.htr 0 3 5 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
                      · linarith only [h540, h569, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h569, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                      · linarith only [h0, h539, h540, h566, h568, h572, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h0, h539, h566, h568, h572, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h566, h567, hc35, hlam, hphi, u3ehi3]
                · linarith only [h536, h538, h566, hlam]
              · linarith only [h0, h539, h565, hlam]
            · linarith only [h0, h538, h564, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h579 | h579
          · rcases m.htr 0 2 4 (by decide) (by decide) with h580 | h580
            · rcases m.htr 0 2 5 (by decide) (by decide) with h581 | h581
              · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
                · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h584 | h584
                    · linarith only [h538, h539, h584, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h587 | h587
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h589 | h589
                            · linarith only [h538, h582, h584, h589, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                              · linarith only [h579, h591, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h536, h582, h586, h591, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                          · linarith only [h536, h583, h588, hlam]
                        · linarith only [h536, h583, h586, h587, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi4]
                      · linarith only [h0, h538, h582, h586, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h582, h583, hc35, hlam, hphi, u3ehi3]
                · linarith only [h536, h538, h582, hlam]
              · linarith only [h579, h581, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h579, h580, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h601 | h601
            · rcases m.htr 0 2 5 (by decide) (by decide) with h602 | h602
              · rcases m.htr 0 3 4 (by decide) (by decide) with h603 | h603
                · rcases m.htr 0 3 5 (by decide) (by decide) with h604 | h604
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h605 | h605
                    · linarith only [h538, h539, h605, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
                      · linarith only [h579, h601, h607, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h607, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h603, h604, hc35, hlam, hphi, u3ehi3]
                · linarith only [h536, h538, h603, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h612 | h612
                · rcases m.htr 0 3 5 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h614 | h614
                    · linarith only [h0, h538, h602, h614, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h616 | h616
                      · linarith only [h0, h579, h616, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h538, h612, h616, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                  · linarith only [h612, h613, hc35, hlam, hphi, u3ehi3]
                · linarith only [h536, h538, h612, hlam]
            · linarith only [h0, h538, h601, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h622 | h622
        · rcases m.htr 0 2 3 (by decide) (by decide) with h623 | h623
          · rcases m.htr 0 2 4 (by decide) (by decide) with h624 | h624
            · rcases m.htr 0 2 5 (by decide) (by decide) with h625 | h625
              · rcases m.htr 0 3 4 (by decide) (by decide) with h626 | h626
                · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h628 | h628
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h631 | h631
                          · linarith only [h536, h622, h629, h631, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                          · linarith only [h536, h626, h631, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h624, h630, hlam]
                      · linarith only [h0, h623, h626, h629, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                    · linarith only [h538, h622, h628, hlam]
                  · linarith only [h626, h627, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h626, h638, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h536, h622, h638, hlam]
              · linarith only [h623, h625, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h623, h624, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h643 | h643
            · rcases m.htr 0 2 5 (by decide) (by decide) with h644 | h644
              · rcases m.htr 0 3 4 (by decide) (by decide) with h645 | h645
                · rcases m.htr 0 3 5 (by decide) (by decide) with h646 | h646
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h647 | h647
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
                      · linarith only [h623, h648, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h648, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h538, h622, h647, hlam]
                  · linarith only [h645, h646, hc35, hlam, hphi, u3ehi3]
                · linarith only [h623, h643, h645, hlam]
              · linarith only [h538, h622, h643, h644, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h655 | h655
              · rcases m.htr 0 3 4 (by decide) (by decide) with h656 | h656
                · rcases m.htr 0 3 5 (by decide) (by decide) with h657 | h657
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                      · linarith only [h623, h659, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h622, h657, h659, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                    · linarith only [h0, h622, h643, h658, hlam]
                  · linarith only [h656, h657, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
                  · linarith only [h656, h664, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h536, h622, h664, hlam]
              · linarith only [h0, h622, h655, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h668 | h668
          · rcases m.htr 0 2 4 (by decide) (by decide) with h669 | h669
            · rcases m.htr 0 2 5 (by decide) (by decide) with h670 | h670
              · rcases m.htr 0 3 4 (by decide) (by decide) with h671 | h671
                · rcases m.htr 0 3 5 (by decide) (by decide) with h672 | h672
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h673 | h673
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h676 | h676
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h677 | h677
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h678 | h678
                              · linarith only [h668, h678, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h0, h668, h671, h678, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · linarith only [h538, h673, h677, hlam]
                          · linarith only [h536, h671, h676, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h669, h675, hlam]
                      · linarith only [h0, h668, h671, h674, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h686 | h686
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                            · linarith only [h538, h673, h686, h688, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
                              · linarith only [h668, h690, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                              · linarith only [h538, h671, h688, h690, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h536, h672, h687, hlam]
                        · linarith only [h0, h668, h671, h686, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                      · linarith only [h0, h685, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h671, h672, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h697 | h697
                  · linarith only [h671, h697, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h699 | h699
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h701 | h701
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h702 | h702
                          · linarith only [h697, h700, h702, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                              · linarith only [h668, h671, h705, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h707 | h707
                                · linarith only [h669, h702, h705, h707, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h709 | h709
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h710 | h710
                                    · rcases h0bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [hlam, p711_0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h536, hlam, p711_0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h538, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h622, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht12, p711_1, u2elo1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [hlam, p711_0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p711_1, u2elo1, u3ehi0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, h668, h697, h699, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p711_1, u2elo1, u3ehi2]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, h668, h697, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p711_1, u2elo1, u3ehi2]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h536, h702, h710, hc01, hc34, hlam, hphi, ht12, ht23, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h668, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [hlam, p711_0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h671, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h697, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h538, hc01, hc14, hlam, hphi, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h669, hlam, p711_0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, h669, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p711_1, u2elo1, u3ehi0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [hlam, p711_0]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, h668, h669, h697, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p711_1, u2elo1, u3ehi2]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h622, hc01, hc15, hlam, hphi, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h670, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h0, h668, h670, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p711_1, u2elo1, u3ehi2]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [h699, hlam, p711_1]
                                      · have p711_0 := h711c.1
                                        have p711_1 := h711c.2.1
                                        have p711_2 := h711c.2.2.1
                                        have p711_3 := h711c.2.2.2
                                        linarith only [hlam, p711_0]
                                    · linarith only [h0, h669, h709, h710, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · linarith only [h0, h669, h699, h705, h709, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                            · linarith only [h0, h538, h669, h699, h704, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h0, h701, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h668, h700, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h743 | h743
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h744 | h744
                          · linarith only [h668, h697, h742, h744, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h746 | h746
                            · linarith only [h538, h699, h743, h746, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h748 | h748
                              · linarith only [h536, h668, h744, h748, hc35, hlam, hphi, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h750 | h750
                                · linarith only [h0, h536, h669, h744, h748, h750, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h752 | h752
                                  · linarith only [h538, h746, h752, hc01, hlam, hphi, ht12, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                                    · linarith only [h538, h746, h754, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h671, h754, hc45, hlam, hphi, ht34, u3ehi0]
                        · linarith only [h0, h743, hc01, hlam, hphi, ht12, u2elo3]
                      · linarith only [h0, h668, h671, h742, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h668, h670, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
            · linarith only [h668, h669, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h761 | h761
            · rcases m.htr 0 2 5 (by decide) (by decide) with h762 | h762
              · rcases m.htr 0 3 4 (by decide) (by decide) with h763 | h763
                · rcases m.htr 0 3 5 (by decide) (by decide) with h764 | h764
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h765 | h765
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
                      · linarith only [h668, h766, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h766, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                      · linarith only [h668, h769, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h769, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h763, h764, hc35, hlam, hphi, u3ehi3]
                · linarith only [h668, h761, h763, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h774 | h774
                · rcases m.htr 0 3 5 (by decide) (by decide) with h775 | h775
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h776 | h776
                    · linarith only [h761, h762, h776, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                      · linarith only [h668, h778, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h778, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h774, h775, hc35, hlam, hphi, u3ehi3]
                · linarith only [h668, h761, h774, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
              · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
                · rcases m.htr 0 3 5 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h787 | h787
                      · linarith only [h668, h787, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h787, hc01, hlam, hphi, ht12, u2elo2]
                    · linarith only [h761, h783, h786, hlam]
                  · linarith only [h784, h785, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h792 | h792
                  · linarith only [h784, h792, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h668, h783, h792, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h795 | h795
                · rcases m.htr 0 3 5 (by decide) (by decide) with h796 | h796
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h797 | h797
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h798 | h798
                      · linarith only [h668, h798, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h798, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
                      · linarith only [h668, h795, h801, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                      · linarith only [h0, h801, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h795, h796, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h805 | h805
                  · linarith only [h795, h805, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h807 | h807
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h808 | h808
                      · linarith only [h0, h668, h808, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h808, hc01, hlam, hphi, ht12, u2elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
                      · linarith only [h0, h668, h811, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h811, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
