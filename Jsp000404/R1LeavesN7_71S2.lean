import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
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
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h18, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h14, h17, h3, hc24, hlam, hphi, ht45, u5elo0]
                                  · linarith only [h16, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h15, h7, hc23, hlam, hphi, u3elo0]
                              · linarith only [h14, h9, hc14, hlam, hphi, ht45, u5elo0]
                            · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h12, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h10, h11, h5, h7, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
                                    · linarith only [h10, h28, h34, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                                    · linarith only [h32, h34, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h10, h28, h32, h33, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h10, h28, h32, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                              · linarith only [h31, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h30, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h28, h29, hc24, hlam, hphi, ht45, u5elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
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
                                          linarith only [h28, h4, h42, h46, h48, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          linarith only [h28, h42, h46, h48, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          linarith only [h28, h42, h46, h48, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          rcases p49_3 (m.d 0 1) (by simp) with h54 | h54
                                          · rcases p49_3 (m.d 0 2) (by simp) with h55 | h55
                                            · linarith only [h0, h55, hlam]
                                            · linarith only [h55, h6, hlam]
                                          · linarith only [h3, h54, hlam]
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
                                          linarith only [h28, h42, h46, h48, h5, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          linarith only [h0, h28, h42, h46, h48, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p49_1]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          rcases p49_3 (m.d 0 1) (by simp) with h63 | h63
                                          · rcases p49_3 (m.d 0 2) (by simp) with h64 | h64
                                            · rcases p49_3 (m.d 0 3) (by simp) with h65 | h65
                                              · linarith only [h4, h65, hlam]
                                              · linarith only [h65, h8, hlam]
                                            · linarith only [h6, h64, hlam]
                                          · linarith only [h3, h63, hlam]
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
                                          linarith only [h28, h42, h46, h48, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p49_1, u3elo0]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          rcases p49_3 (m.d 0 1) (by simp) with h74 | h74
                                          · rcases p49_3 (m.d 0 2) (by simp) with h75 | h75
                                            · rcases p49_3 (m.d 0 3) (by simp) with h76 | h76
                                              · rcases p49_3 (m.d 0 4) (by simp) with h77 | h77
                                                · linarith only [h7, h77, hlam]
                                                · linarith only [h77, h9, hlam]
                                              · linarith only [h76, h8, hlam]
                                            · linarith only [h6, h75, hlam]
                                          · linarith only [h3, h74, hlam]
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
                                          linarith only [h7, hlam, p49_0]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          linarith only [hlam, p49_0]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          rcases p49_3 (m.d 0 1) (by simp) with h87 | h87
                                          · rcases p49_3 (m.d 0 2) (by simp) with h88 | h88
                                            · rcases p49_3 (m.d 0 3) (by simp) with h89 | h89
                                              · rcases p49_3 (m.d 0 4) (by simp) with h90 | h90
                                                · rcases p49_3 (m.d 0 5) (by simp) with h91 | h91
                                                  · linarith only [h9, h91, hlam]
                                                  · rcases h0emin with h93 | h93 | h93 | h93 | h93
                                                    · rcases h2bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        rcases p94_3 (m.d 0 2) (by simp) with h96 | h96
                                                        · rcases p94_3 (m.d 1 2) (by simp) with h97 | h97
                                                          · linarith only [h0, h97, hlam]
                                                          · rcases p94_3 (m.d 2 3) (by simp) with h99 | h99
                                                            · linarith only [h4, h99, hlam]
                                                            · linarith only [h10, h99, hlam]
                                                        · linarith only [h0, h96, hlam]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h0, h28, h42, h45, h46, h48, hc01, hc45, hlam, hphi, ht0b, ht5b, p94_1]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h0, h28, h42, h46, h48, hc01, hc45, hlam, hphi, ht0b, ht5b, p94_1]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h28, h4, h42, h45, hlam, p94_2]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h0, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h10, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h28, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h28, h45, h46, h48, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo2]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h4, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h4, hc12, hlam, hphi, ht23, p94_1, u3elo0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h28, h4, hc12, hlam, hphi, ht23, p94_1, u3elo0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        rcases p94_3 (m.d 0 2) (by simp) with h115 | h115
                                                        · rcases p94_3 (m.d 1 2) (by simp) with h116 | h116
                                                          · linarith only [h10, h116, hlam]
                                                          · linarith only [h116, h42, hlam]
                                                        · linarith only [h115, h6, hlam]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h5, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h42, h46, h48, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p94_1]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h45, hlam, p94_1]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        rcases p94_3 (m.d 0 2) (by simp) with h124 | h124
                                                        · rcases p94_3 (m.d 1 2) (by simp) with h125 | h125
                                                          · linarith only [h125, h28, hlam]
                                                          · linarith only [h125, h42, hlam]
                                                        · linarith only [h124, h6, hlam]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h6, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h42, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h46, hlam, p94_1]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [h47, hlam, p94_0]
                                                      · have p94_0 := h94c.1
                                                        have p94_1 := h94c.2.1
                                                        have p94_2 := h94c.2.2.1
                                                        have p94_3 := h94c.2.2.2
                                                        linarith only [hlam, p94_0]
                                                    · rcases h2bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        rcases p134_3 (m.d 0 2) (by simp) with h136 | h136
                                                        · rcases p134_3 (m.d 1 2) (by simp) with h137 | h137
                                                          · linarith only [h0, h137, hlam]
                                                          · rcases p134_3 (m.d 2 3) (by simp) with h139 | h139
                                                            · linarith only [h139, h4, hlam]
                                                            · linarith only [h10, h139, hlam]
                                                        · linarith only [h0, h136, hlam]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h0, h10, h42, h46, h48, hc01, hc45, hlam, hphi, ht0b, ht5b, p134_1]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h0, h28, h42, h46, h48, hc01, hc45, hlam, hphi, ht0b, ht5b, p134_1]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h10, h4, h42, hlam, p134_2]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h0, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h10, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h28, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h10, h46, h48, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p134_1, u3elo2]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h4, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [hc12, hlam, hphi, ht23, p134_1, u3elo2]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h28, h4, h42, h46, h48, hc02, hc45, hlam, hphi, ht0b, ht5b, p134_1]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        rcases p134_3 (m.d 0 2) (by simp) with h155 | h155
                                                        · rcases p134_3 (m.d 1 2) (by simp) with h156 | h156
                                                          · linarith only [h10, h156, hlam]
                                                          · linarith only [h156, h42, hlam]
                                                        · linarith only [h155, h6, hlam]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h5, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h0, h42, h46, h48, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p134_1]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h45, hlam, p134_1]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        rcases p134_3 (m.d 0 2) (by simp) with h164 | h164
                                                        · rcases p134_3 (m.d 1 2) (by simp) with h165 | h165
                                                          · linarith only [h165, h28, hlam]
                                                          · linarith only [h165, h42, hlam]
                                                        · linarith only [h164, h6, hlam]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h6, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h42, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h46, hlam, p134_1]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [h47, hlam, p134_0]
                                                      · have p134_0 := h134c.1
                                                        have p134_1 := h134c.2.1
                                                        have p134_2 := h134c.2.2.1
                                                        have p134_3 := h134c.2.2.2
                                                        linarith only [hlam, p134_0]
                                                    · linarith only [h93, hlam, ht01, ht12, ht23, u3elo0]
                                                    · linarith only [h7, h93, hlam, ht01, ht12, ht23, u3elo0]
                                                    · linarith only [h7, h93, hlam, ht01, ht12, ht23, p49_1, u3elo0]
                                                · linarith only [h9, h90, hlam]
                                              · linarith only [h8, h89, hlam]
                                            · linarith only [h6, h88, hlam]
                                          · linarith only [h3, h87, hlam]
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
                                          linarith only [h8, hlam, p49_0]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          linarith only [h9, hlam, p49_1]
                                        · have p49_0 := h49c.1
                                          have p49_1 := h49c.2.1
                                          have p49_2 := h49c.2.2.1
                                          have p49_3 := h49c.2.2.2
                                          linarith only [hlam, p49_0]
                                      · linarith only [h48, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h47, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h46, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h10, h45, h7, hc13, hlam, hphi, u3elo0]
                              · linarith only [h28, h42, h44, hc25, hlam, hphi, u5elo4]
                            · linarith only [h43, h7, hc13, hlam, hphi, u3elo0]
                          · linarith only [h42, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h9, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h198 | h198
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h200 | h200
                            · linarith only [h195, h200, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                                · linarith only [h195, h197, h203, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h207 | h207
                                      · rcases h0bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h205, h207, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h211 | h211
                                          · rcases p208_3 (m.d 0 2) (by simp) with h212 | h212
                                            · linarith only [h0, h212, hlam]
                                            · linarith only [h212, h4, hlam]
                                          · linarith only [h1, h211, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h216 | h216
                                          · rcases p208_3 (m.d 0 2) (by simp) with h217 | h217
                                            · linarith only [h0, h217, hlam]
                                            · linarith only [h217, h5, hlam]
                                          · linarith only [h2, h216, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h221 | h221
                                          · rcases p208_3 (m.d 0 2) (by simp) with h222 | h222
                                            · linarith only [h0, h222, hlam]
                                            · linarith only [h222, h6, hlam]
                                          · linarith only [h221, h3, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h0, hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h228 | h228
                                          · rcases p208_3 (m.d 0 2) (by simp) with h229 | h229
                                            · rcases p208_3 (m.d 0 3) (by simp) with h230 | h230
                                              · linarith only [h230, h4, hlam]
                                              · rcases p208_3 (m.d 0 4) (by simp) with h232 | h232
                                                · linarith only [h232, h5, hlam]
                                                · linarith only [h232, h7, hlam]
                                            · linarith only [h229, h4, hlam]
                                          · linarith only [h1, h228, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h237 | h237
                                          · rcases p208_3 (m.d 0 2) (by simp) with h238 | h238
                                            · rcases p208_3 (m.d 0 3) (by simp) with h239 | h239
                                              · linarith only [h239, h4, hlam]
                                              · rcases p208_3 (m.d 0 4) (by simp) with h241 | h241
                                                · linarith only [h241, h5, hlam]
                                                · rcases p208_3 (m.d 0 5) (by simp) with h243 | h243
                                                  · linarith only [h243, h6, hlam]
                                                  · rcases h0emin with h245 | h245 | h245 | h245 | h245
                                                    · rcases h2bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h0, h198, h203, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        rcases p246_3 (m.d 0 2) (by simp) with h249 | h249
                                                        · rcases p246_3 (m.d 1 2) (by simp) with h250 | h250
                                                          · linarith only [h0, h250, hlam]
                                                          · linarith only [h197, h250, hlam]
                                                        · linarith only [h249, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        rcases p246_3 (m.d 0 2) (by simp) with h254 | h254
                                                        · rcases p246_3 (m.d 1 2) (by simp) with h255 | h255
                                                          · linarith only [h0, h255, hlam]
                                                          · linarith only [h198, h255, hlam]
                                                        · linarith only [h254, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        rcases p246_3 (m.d 0 2) (by simp) with h259 | h259
                                                        · rcases p246_3 (m.d 1 2) (by simp) with h260 | h260
                                                          · linarith only [h0, h260, hlam]
                                                          · linarith only [h199, h260, hlam]
                                                        · linarith only [h259, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h0, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h0, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h0, h203, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        rcases p246_3 (m.d 0 2) (by simp) with h268 | h268
                                                        · rcases p246_3 (m.d 1 2) (by simp) with h269 | h269
                                                          · rcases p246_3 (m.d 2 3) (by simp) with h270 | h270
                                                            · linarith only [h197, h270, hlam]
                                                            · linarith only [h205, h270, hlam]
                                                          · linarith only [h269, hlam, p246_0]
                                                        · linarith only [h268, h6, hlam]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h4, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h197, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h203, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h1, h197, h7, hc02, hc25, hlam, hphi, ht0b, ht5b, p208_1, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h5, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h198, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p208_1, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h0, h198, h2, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h6, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h199, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h205, hlam, p246_1]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [h206, hlam, p246_0]
                                                      · have p246_0 := h246c.1
                                                        have p246_1 := h246c.2.1
                                                        have p246_2 := h246c.2.2.1
                                                        have p246_3 := h246c.2.2.2
                                                        linarith only [hlam, p246_0]
                                                    · rcases h2bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h0, h197, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p290_1]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        rcases p290_3 (m.d 0 2) (by simp) with h293 | h293
                                                        · rcases p290_3 (m.d 1 2) (by simp) with h294 | h294
                                                          · linarith only [h0, h294, hlam]
                                                          · linarith only [h197, h294, hlam]
                                                        · linarith only [h293, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        rcases p290_3 (m.d 0 2) (by simp) with h298 | h298
                                                        · rcases p290_3 (m.d 1 2) (by simp) with h299 | h299
                                                          · linarith only [h0, h299, hlam]
                                                          · linarith only [h198, h299, hlam]
                                                        · linarith only [h298, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        rcases p290_3 (m.d 0 2) (by simp) with h303 | h303
                                                        · rcases p290_3 (m.d 1 2) (by simp) with h304 | h304
                                                          · linarith only [h0, h304, hlam]
                                                          · linarith only [h199, h304, hlam]
                                                        · linarith only [h303, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h0, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h0, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p290_1]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h0, h203, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p290_1]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        rcases p290_3 (m.d 0 2) (by simp) with h312 | h312
                                                        · rcases p290_3 (m.d 1 2) (by simp) with h313 | h313
                                                          · rcases p290_3 (m.d 2 3) (by simp) with h314 | h314
                                                            · linarith only [h197, h314, hlam]
                                                            · linarith only [h205, h314, hlam]
                                                          · linarith only [h313, hlam, p290_0]
                                                        · linarith only [h312, h6, hlam]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h4, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h197, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h203, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h1, h197, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p290_1, u3elo3]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h5, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h198, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p208_1, p290_1]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h0, h198, h2, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1, p290_1]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h6, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h199, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h205, hlam, p290_1]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [h206, hlam, p290_0]
                                                      · have p290_0 := h290c.1
                                                        have p290_1 := h290c.2.1
                                                        have p290_2 := h290c.2.2.1
                                                        have p290_3 := h290c.2.2.2
                                                        linarith only [hlam, p290_0]
                                                    · linarith only [h245, h7, hlam, ht01, ht12, ht23, u3elo3]
                                                    · linarith only [h0, h245, hc01, hlam, p208_1]
                                                    · linarith only [h245, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                            · linarith only [h238, h5, hlam]
                                          · linarith only [h2, h237, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h339 | h339
                                          · rcases p208_3 (m.d 0 2) (by simp) with h340 | h340
                                            · rcases p208_3 (m.d 0 3) (by simp) with h341 | h341
                                              · linarith only [h341, h4, hlam]
                                              · linarith only [h195, h341, hlam]
                                            · linarith only [h340, h6, hlam]
                                          · linarith only [h3, h339, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h1, hlam, p208_1]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h4, hlam, p208_1]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h7, hlam, p208_1]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo3]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h2, hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h5, hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h7, hc03, hlam, hphi, p208_1, u3elo3]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          rcases p208_3 (m.d 0 1) (by simp) with h355 | h355
                                          · rcases p208_3 (m.d 0 2) (by simp) with h356 | h356
                                            · rcases p208_3 (m.d 0 3) (by simp) with h357 | h357
                                              · linarith only [h357, h7, hlam]
                                              · linarith only [h195, h357, hlam]
                                            · linarith only [h356, h6, hlam]
                                          · linarith only [h3, h355, hlam]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h3, hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h6, hlam, p208_1]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h195, hlam, p208_0]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [h196, hlam, p208_1]
                                        · have p208_0 := h208c.1
                                          have p208_1 := h208c.2.1
                                          have p208_2 := h208c.2.2.1
                                          have p208_3 := h208c.2.2.2
                                          linarith only [hlam, p208_0]
                                      · linarith only [h2, h207, h7, hc14, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h206, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h205, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h202, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h199, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h197, h198, h5, h7, hc23, hlam, hphi, u3elo3]
                      · linarith only [h197, h4, h7, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h196, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h195, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h377 | h377
              · rcases m.htr 0 3 4 (by decide) (by decide) with h378 | h378
                · linarith only [h378, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h383 | h383
                        · linarith only [h0, h383, h5, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h385 | h385
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h386 | h386
                            · linarith only [h378, h386, hc03, hlam, hphi, u3elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h388 | h388
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                                · linarith only [h0, h378, h380, h382, h389, hc02, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h389, h4, h5, hc23, hlam, hphi, u3elo3]
                              · linarith only [h388, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h382, h385, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h382, h4, h5, hc12, hc24, hlam, hphi]
                    · linarith only [h381, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h380, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h377, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h398 | h398
            · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
              · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
                · rcases m.htr 0 3 5 (by decide) (by decide) with h401 | h401
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
                      · linarith only [h0, h4, h403, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h409 | h409
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h410 | h410
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                                    · linarith only [h0, h4, h405, h411, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                    · linarith only [h409, h411, hc34, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h0, h4, h405, h409, h410, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · linarith only [h4, h409, hc02, hlam, hphi, ht23, u3elo3]
                              · linarith only [h408, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h4, h400, h407, hc13, hlam, hphi, u3elo2]
                          · linarith only [h406, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h398, h4, h405, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h402, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h401, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h398, h4, h400, hlam]
              · linarith only [h398, h399, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 3 5 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h427 | h427
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                      · linarith only [h0, h4, h428, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                        · linarith only [h398, h428, h430, hc02, hlam, hphi, ht23, u3elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h438 | h438
                                      · rcases h0bigk with h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          rcases p439_3 (m.d 0 1) (by simp) with h441 | h441
                                          · rcases p439_3 (m.d 0 2) (by simp) with h442 | h442
                                            · linarith only [h0, h442, hlam]
                                            · rcases p439_3 (m.d 0 3) (by simp) with h444 | h444
                                              · linarith only [h1, h444, hlam]
                                              · linarith only [h4, h444, hlam]
                                          · linarith only [h0, h441, hlam]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h1, h433, h438, hc01, hc45, hlam, hphi, ht0b, ht5b, p439_1]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          rcases p439_3 (m.d 0 1) (by simp) with h449 | h449
                                          · rcases p439_3 (m.d 0 2) (by simp) with h450 | h450
                                            · linarith only [h0, h450, hlam]
                                            · rcases p439_3 (m.d 0 3) (by simp) with h452 | h452
                                              · linarith only [h1, h452, hlam]
                                              · linarith only [h425, h452, hlam]
                                          · linarith only [h2, h449, hlam]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          rcases p439_3 (m.d 0 1) (by simp) with h456 | h456
                                          · rcases p439_3 (m.d 0 2) (by simp) with h457 | h457
                                            · linarith only [h0, h457, hlam]
                                            · linarith only [h424, h457, hlam]
                                          · linarith only [h3, h456, hlam]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h0, hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h4, hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h398, hlam, p439_1]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h3, h398, h435, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p439_1, u3elo2]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h1, hlam, p439_1]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h4, hc02, hlam, hphi, ht23, p439_1, u3elo2]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h0, h398, h4, h432, h436, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p439_1, u3elo2]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          rcases p439_3 (m.d 0 1) (by simp) with h470 | h470
                                          · rcases p439_3 (m.d 0 2) (by simp) with h471 | h471
                                            · linarith only [h4, h471, hlam]
                                            · linarith only [h424, h471, hlam]
                                          · linarith only [h3, h470, hlam]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h2, hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h0, h398, h432, h435, h436, h438, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p439_1, u3elo2]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h425, hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          rcases p439_3 (m.d 0 1) (by simp) with h479 | h479
                                          · rcases p439_3 (m.d 0 2) (by simp) with h480 | h480
                                            · linarith only [h398, h480, hlam]
                                            · linarith only [h424, h480, hlam]
                                          · linarith only [h3, h479, hlam]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h3, hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h424, hlam, p439_1]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h426, hlam, p439_0]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [h427, hlam, p439_1]
                                        · have p439_0 := h439c.1
                                          have p439_1 := h439c.2.1
                                          have p439_2 := h439c.2.2.1
                                          have p439_3 := h439c.2.2.2
                                          linarith only [hlam, p439_0]
                                      · linarith only [h438, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h398, h437, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                  · linarith only [h0, h398, h432, h435, h436, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                                · linarith only [h0, h4, h432, h435, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h430, h432, h434, hc25, hlam, hphi, u5elo4]
                            · linarith only [h425, h433, hc13, hlam, hphi, u3elo0]
                          · linarith only [h432, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h398, h427, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h426, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h498 | h498
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h499 | h499
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
                      · linarith only [h0, h4, h425, h500, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h502 | h502
                        · linarith only [h0, h398, h502, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h504 | h504
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                            · linarith only [h1, h425, h505, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h507 | h507
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                                · linarith only [h1, h425, h500, h504, h508, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · linarith only [h0, h4, h504, h508, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h500, h504, h505, h507, hc25, hlam, hphi, u5elo4]
                          · linarith only [h504, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h4, h424, h425, h499, hc25, hlam, hphi, u5elo4]
                  · linarith only [h4, h424, h498, hc25, hlam, hphi, u5elo3]
              · linarith only [h424, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h517 | h517
        · rcases m.htr 0 2 3 (by decide) (by decide) with h518 | h518
          · rcases m.htr 0 2 4 (by decide) (by decide) with h519 | h519
            · linarith only [h0, h2, h519, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h521 | h521
              · rcases m.htr 0 3 4 (by decide) (by decide) with h522 | h522
                · linarith only [h1, h2, h522, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h526 | h526
                      · linarith only [h0, h2, h522, h526, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h2, h518, h522, h526, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h2, h525, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1, h524, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h518, h521, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h532 | h532
            · linarith only [h0, h2, h532, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h534 | h534
              · rcases m.htr 0 3 4 (by decide) (by decide) with h535 | h535
                · linarith only [h1, h2, h535, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
                      · linarith only [h0, h518, h535, h539, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h541 | h541
                        · linarith only [h1, h2, h532, h539, h541, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h543 | h543
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h544 | h544
                            · linarith only [h1, h2, h535, h544, hlam]
                            · linarith only [h1, h2, h539, h543, h544, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h543, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h2, h538, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h518, h537, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h534, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h517, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h553 | h553
    · rcases m.htr 0 1 4 (by decide) (by decide) with h554 | h554
      · rcases m.htr 0 1 5 (by decide) (by decide) with h555 | h555
        · rcases m.htr 0 2 3 (by decide) (by decide) with h556 | h556
          · rcases m.htr 0 2 4 (by decide) (by decide) with h557 | h557
            · rcases m.htr 0 2 5 (by decide) (by decide) with h558 | h558
              · rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
                · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h566 | h566
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                      · linarith only [h0, h553, h562, h567, h570, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h570, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h569, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h568, hc23, hlam, hphi, ht34, ht45, u5elo3]
                                · linarith only [h559, h567, hc23, hlam, hphi, u3elo0]
                              · linarith only [h566, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h559, h565, hc13, hlam, hphi, u3elo0]
                          · linarith only [h0, h564, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h553, h557, h562, h563, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h553, h562, hc13, hlam, hphi, u3elo2]
                    · linarith only [h561, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h560, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h584 | h584
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h585 | h585
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h587 | h587
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                            · linarith only [h553, h559, h583, h588, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h590 | h590
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                                · linarith only [h559, h583, h591, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h593 | h593
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h594 | h594
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h595 | h595
                                      · rcases h0bigk with h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h0, hlam, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h0, h553, h585, h593, h595, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h0, h553, h559, h585, h593, h595, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          rcases p596_3 (m.d 0 1) (by simp) with h601 | h601
                                          · rcases p596_3 (m.d 0 2) (by simp) with h602 | h602
                                            · rcases p596_3 (m.d 0 3) (by simp) with h603 | h603
                                              · linarith only [h553, h603, hlam]
                                              · linarith only [h583, h603, hlam]
                                            · linarith only [h558, h602, hlam]
                                          · linarith only [h555, h601, hlam]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h0, h553, h585, h593, h595, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          rcases p596_3 (m.d 0 1) (by simp) with h610 | h610
                                          · linarith only [h0, h610, hlam]
                                          · linarith only [h553, h610, hlam]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          rcases p596_3 (m.d 0 1) (by simp) with h613 | h613
                                          · linarith only [h0, h613, hlam]
                                          · linarith only [h554, h613, hlam]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          rcases p596_3 (m.d 0 1) (by simp) with h616 | h616
                                          · linarith only [h0, h616, hlam]
                                          · linarith only [h555, h616, hlam]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h553, hlam, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h556, hlam, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h559, hlam, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h555, h559, h587, h593, h595, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p596_1, u3elo3]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h554, hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h557, hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h559, hc03, hlam, hphi, p596_1, u3elo3]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          rcases p596_3 (m.d 0 1) (by simp) with h628 | h628
                                          · rcases p596_3 (m.d 0 2) (by simp) with h629 | h629
                                            · rcases p596_3 (m.d 0 3) (by simp) with h630 | h630
                                              · linarith only [h559, h630, hlam]
                                              · linarith only [h583, h630, hlam]
                                            · linarith only [h558, h629, hlam]
                                          · linarith only [h555, h628, hlam]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h555, hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h558, hlam, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h583, hlam, p596_0]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [h584, hlam, p596_1]
                                        · have p596_0 := h596c.1
                                          have p596_1 := h596c.2.1
                                          have p596_2 := h596c.2.2.1
                                          have p596_3 := h596c.2.2.2
                                          linarith only [hlam, p596_0]
                                      · linarith only [h559, h595, hc04, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h555, h590, h594, hc24, hlam, hphi, ht45, u5elo0]
                                  · linarith only [h593, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h590, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h587, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h553, h557, h585, h586, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h585, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h559, h583, h584, hc35, hlam, hphi, u5elo4]
                  · linarith only [h583, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h558, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h554, h557, hlam]
          · linarith only [h0, h553, h556, hc13, hlam, hphi, u3elo2]
        · linarith only [h553, h555, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h653 | h653
        · rcases m.htr 0 2 3 (by decide) (by decide) with h654 | h654
          · rcases m.htr 0 2 4 (by decide) (by decide) with h655 | h655
            · rcases m.htr 0 2 5 (by decide) (by decide) with h656 | h656
              · rcases m.htr 0 3 4 (by decide) (by decide) with h657 | h657
                · linarith only [h553, h554, h657, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h659 | h659
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h660 | h660
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h662 | h662
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                            · linarith only [h553, h554, h657, h662, h664, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h553, h554, h664, hc13, hlam, hphi, u3elo3]
                          · linarith only [h663, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h553, h655, h661, h662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h661, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h660, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h659, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h656, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h673 | h673
              · rcases m.htr 0 3 4 (by decide) (by decide) with h674 | h674
                · linarith only [h0, h553, h655, h674, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h677 | h677
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
                            · linarith only [h0, h553, h655, h674, h679, h681, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h553, h655, h679, h681, hc13, hlam, hphi, u3elo3]
                          · linarith only [h0, h553, h655, h678, h679, h680, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h686 | h686
                            · linarith only [h0, h553, h655, h674, h679, h686, hc02, hc24, hlam, hphi]
                            · linarith only [h553, h554, h678, h686, hc23, hlam, hphi, u3elo3]
                          · linarith only [h0, h553, h678, h685, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h0, h553, h678, hc13, hlam, hphi, u3elo2]
                    · linarith only [h0, h553, h655, h677, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h676, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h553, h673, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h553, h654, hc13, hlam, hphi, u3elo2]
        · linarith only [h553, h653, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h696 | h696
      · rcases m.htr 0 1 5 (by decide) (by decide) with h697 | h697
        · rcases m.htr 0 2 3 (by decide) (by decide) with h698 | h698
          · rcases m.htr 0 2 4 (by decide) (by decide) with h699 | h699
            · rcases m.htr 0 2 5 (by decide) (by decide) with h700 | h700
              · rcases m.htr 0 3 4 (by decide) (by decide) with h701 | h701
                · rcases m.htr 0 3 5 (by decide) (by decide) with h702 | h702
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h706 | h706
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h707 | h707
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h708 | h708
                              · linarith only [h553, h696, h708, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h705, h708, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h553, h696, h705, h707, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h0, h700, h706, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h553, h696, h699, h704, h705, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h696, h704, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h703, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h553, h696, h702, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h553, h696, h701, hlam]
              · linarith only [h553, h696, h698, h700, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h553, h696, h698, h699, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h720 | h720
            · rcases m.htr 0 2 5 (by decide) (by decide) with h721 | h721
              · rcases m.htr 0 3 4 (by decide) (by decide) with h722 | h722
                · rcases m.htr 0 3 5 (by decide) (by decide) with h723 | h723
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h724 | h724
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h726 | h726
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h727 | h727
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h729 | h729
                              · linarith only [h553, h696, h729, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h726, h729, hc24, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h696, h698, h725, h726, h728, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h0, h698, h725, h727, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h698, h720, h725, h726, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h0, h696, h725, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h724, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h723, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h696, h698, h722, hlam]
              · linarith only [h0, h696, h721, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h696, h720, hlam]
        · linarith only [h696, h697, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h742 | h742
        · rcases m.htr 0 2 3 (by decide) (by decide) with h743 | h743
          · rcases m.htr 0 2 4 (by decide) (by decide) with h744 | h744
            · rcases m.htr 0 2 5 (by decide) (by decide) with h745 | h745
              · rcases m.htr 0 3 4 (by decide) (by decide) with h746 | h746
                · rcases m.htr 0 3 5 (by decide) (by decide) with h747 | h747
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h748 | h748
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h749 | h749
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h750 | h750
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h753 | h753
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h754 | h754
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h755 | h755
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h756 | h756
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h757 | h757
                                      · rcases h0bigk with h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h0, hlam, p758_1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h553, hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h696, hlam, p758_1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h696, h752, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p758_1, u3elo1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          rcases p758_3 (m.d 0 1) (by simp) with h764 | h764
                                          · linarith only [h0, h764, hlam]
                                          · rcases p758_3 (m.d 0 2) (by simp) with h766 | h766
                                            · rcases p758_3 (m.d 0 3) (by simp) with h767 | h767
                                              · linarith only [h743, h767, hlam]
                                              · linarith only [h553, h767, hlam]
                                            · linarith only [h0, h766, hlam]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h743, h754, h757, hc02, hc45, hlam, hphi, ht0b, ht5b, p758_1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          rcases p758_3 (m.d 0 1) (by simp) with h773 | h773
                                          · linarith only [h0, h773, hlam]
                                          · rcases p758_3 (m.d 0 2) (by simp) with h775 | h775
                                            · rcases p758_3 (m.d 0 3) (by simp) with h776 | h776
                                              · linarith only [h743, h776, hlam]
                                              · linarith only [h746, h776, hlam]
                                            · linarith only [h744, h775, hlam]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          rcases p758_3 (m.d 0 1) (by simp) with h780 | h780
                                          · linarith only [h0, h780, hlam]
                                          · linarith only [h742, h780, hlam]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, p758_1, u3elo0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h743, hlam, p758_1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h553, h696, h742, h751, h755, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p758_1, u3elo1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          rcases p758_3 (m.d 0 1) (by simp) with h787 | h787
                                          · linarith only [h553, h787, hlam]
                                          · linarith only [h742, h787, hlam]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h696, h742, h751, h752, h755, h757, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p758_1, u3elo1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h744, hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h746, hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          rcases p758_3 (m.d 0 1) (by simp) with h794 | h794
                                          · linarith only [h696, h794, hlam]
                                          · linarith only [h742, h794, hlam]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h742, hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h745, hlam, p758_1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h747, hlam, p758_0]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [h748, hlam, p758_1]
                                        · have p758_0 := h758c.1
                                          have p758_1 := h758c.2.1
                                          have p758_2 := h758c.2.2.1
                                          have p758_3 := h758c.2.2.2
                                          linarith only [hlam, p758_0]
                                      · linarith only [h757, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h742, h753, h756, hc24, hlam, hphi, ht45, u5elo0]
                                  · linarith only [h754, h755, hc34, hlam, hphi, ht45, u5elo3]
                                · linarith only [h553, h746, h754, hc23, hlam, hphi, u3elo1]
                              · linarith only [h696, h753, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h553, h746, h752, hlam]
                          · linarith only [h751, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h744, h750, hlam]
                      · linarith only [h0, h749, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h696, h742, h748, hc15, hlam, hphi, u5elo4]
                  · linarith only [h696, h742, h746, h747, hc15, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h813 | h813
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h814 | h814
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h815 | h815
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h817 | h817
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h818 | h818
                            · linarith only [h553, h742, h746, h817, h818, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h553, h742, h817, h818, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h553, h742, h815, h817, hc15, hlam, hphi, u5elo2]
                        · linarith only [h0, h744, h816, hlam]
                      · linarith only [h0, h742, h815, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h553, h742, h746, h814, hc15, hlam, hphi, u5elo4]
                  · linarith only [h553, h742, h813, hc15, hlam, hphi, u5elo3]
              · linarith only [h743, h745, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h827 | h827
              · rcases m.htr 0 3 4 (by decide) (by decide) with h828 | h828
                · linarith only [h743, h744, h828, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h830 | h830
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h831 | h831
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h832 | h832
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h833 | h833
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h834 | h834
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h835 | h835
                            · linarith only [h553, h742, h828, h834, h835, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h553, h742, h834, h835, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h744, h833, h834, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                            · linarith only [h553, h742, h828, h839, h840, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h553, h742, h839, h840, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h839, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h0, h742, h743, h832, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h744, h831, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h830, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h743, h827, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h848 | h848
            · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
              · rcases m.htr 0 3 4 (by decide) (by decide) with h850 | h850
                · rcases m.htr 0 3 5 (by decide) (by decide) with h851 | h851
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h852 | h852
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h854 | h854
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h856 | h856
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h857 | h857
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h858 | h858
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h859 | h859
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h860 | h860
                                    · linarith only [h743, h848, h853, h860, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                    · linarith only [h860, hc24, hlam, hphi, ht45, u5elo4]
                                  · linarith only [h743, h859, hc02, hlam, hphi, ht23, u3elo4]
                                · linarith only [h696, h742, h743, h848, h855, h858, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h857, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h696, h742, h743, h848, h853, h855, h856, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h855, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h743, h848, h853, h854, hlam]
                      · linarith only [h0, h742, h853, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h696, h742, h852, hc15, hlam, hphi, u5elo4]
                  · linarith only [h851, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h743, h848, h850, hlam]
              · linarith only [h696, h742, h848, h849, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h874 | h874
              · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
                · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h879 | h879
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h880 | h880
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h882 | h882
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h883 | h883
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h884 | h884
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                                      · rcases h0bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h0, hlam, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h553, hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h696, hlam, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h0, h848, h878, h883, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h848, h878, h883, hc01, hc12, hlam, hphi, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h743, hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h848, hlam, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h742, h848, h880, h883, h884, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1, u3elo2]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h553, h742, h880, h884, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1, u3elo1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h553, hc02, hlam, hphi, ht23, p887_1, u3elo1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h553, h696, h742, h880, h884, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1, u3elo1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          rcases p887_3 (m.d 0 1) (by simp) with h902 | h902
                                          · linarith only [h553, h902, hlam]
                                          · linarith only [h742, h902, hlam]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h696, h742, h880, h881, h884, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1, u3elo1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h0, h742, h848, h878, h880, h883, h884, h886, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1, u3elo1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h875, hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          rcases p887_3 (m.d 0 1) (by simp) with h909 | h909
                                          · linarith only [h696, h909, hlam]
                                          · linarith only [h742, h909, hlam]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h742, hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h874, hlam, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h876, hlam, p887_0]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [h877, hlam, p887_1]
                                        · have p887_0 := h887c.1
                                          have p887_1 := h887c.2.1
                                          have p887_2 := h887c.2.2.1
                                          have p887_3 := h887c.2.2.2
                                          linarith only [hlam, p887_0]
                                      · linarith only [h886, hc34, hlam, hphi, ht45, u5elo4]
                                    · linarith only [h0, h742, h848, h882, h885, hlam]
                                  · linarith only [h0, h848, h883, h884, hc01, hlam, hphi, ht12, ht23, u3elo4]
                                · linarith only [h0, h742, h743, h880, h883, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h882, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h875, h881, hc13, hlam, hphi, u3elo0]
                          · linarith only [h880, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h742, h743, h878, h879, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h742, h878, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h877, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h876, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h928 | h928
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h929 | h929
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h931 | h931
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h932 | h932
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h933 | h933
                            · linarith only [h0, h742, h743, h875, h932, h933, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h553, h742, h932, h933, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                          · linarith only [h743, h930, h932, hc02, hc25, hlam, hphi]
                        · linarith only [h0, h742, h743, h930, h931, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h742, h930, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h0, h742, h743, h875, h929, hc15, hlam, hphi, u5elo4]
                  · linarith only [h0, h742, h743, h928, hc15, hlam, hphi, u5elo3]
              · linarith only [h0, h742, h874, hc15, hlam, hphi, u5elo2]
        · linarith only [h742, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
