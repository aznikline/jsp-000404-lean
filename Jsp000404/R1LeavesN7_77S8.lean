import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_R_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h5elo := hb5.1
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
                                      · linarith only [h0, h10, h15, h17, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h17, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                                  · linarith only [h16, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                                · linarith only [h0, h10, h13, h15, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h11, h14, h9, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                                · linarith only [h0, h10, h13, h26, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                                      · rcases h0bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h1, h10, h28, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h11, h2, h26, h28, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h12, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h1, h10, h28, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h11, h2, h26, h28, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h12, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h1, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h4, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h11, h2, h26, h28, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h0, h12, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h2, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h5, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h7, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h12, h3, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p31_1, u2ehi4]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h3, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h6, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h8, hlam, p31_0]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [h9, hlam, p31_1]
                                        · have p31_0 := h31c.1
                                          have p31_1 := h31c.2.1
                                          have p31_2 := h31c.2.2.1
                                          have p31_3 := h31c.2.2.2
                                          linarith only [hlam, p31_0]
                                      · linarith only [h10, h13, h28, h30, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h26, h28, h29, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                                  · linarith only [h28, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                              · linarith only [h11, h25, h9, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo0]
                          · linarith only [h11, h12, hc25, hlam, hphi, u2ehi3]
                        · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                        · linarith only [h10, h63, hc23, hlam, hphi, u2ehi3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h0, h10, h4, h65, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                          · linarith only [h65, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
                    · linarith only [h5, h9, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h4, h8, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                            · linarith only [h1, h7, h75, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h77 | h77
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                                · linarith only [h3, h7, h70, h72, h74, h78, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h82 | h82
                                      · rcases h0bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, h70, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, h7, h70, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h0, hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, h70, h74, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h0, h3, h7, h70, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h0, h3, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h1, hlam, p83_1]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h4, hlam, p83_1]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h7, hlam, p83_1]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, h74, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h2, hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h5, hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h2, h4, h80, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, h7, h74, hc34, hlam, hphi, ht23, p83_1, u2ehi4]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h3, hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h6, hlam, p83_1]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h70, hlam, p83_0]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [h71, hlam, p83_1]
                                        · have p83_0 := h83c.1
                                          have p83_1 := h83c.2.1
                                          have p83_2 := h83c.2.2.1
                                          have p83_3 := h83c.2.2.2
                                          linarith only [hlam, p83_0]
                                      · linarith only [h5, h7, h78, h80, h82, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                                    · linarith only [h78, h80, h81, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                                  · linarith only [h80, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                              · linarith only [h7, h70, h71, h73, h77, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h74, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
                        · linarith only [h72, h73, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h4, h7, h72, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h5, h71, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h4, h70, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h6, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
            · linarith only [h120, h4, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
              · linarith only [h122, h4, hc23, hlam, hphi, u2ehi4]
              · linarith only [h122, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · linarith only [h0, h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h126 | h126
        · rcases m.htr 0 2 3 (by decide) (by decide) with h127 | h127
          · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
            · linarith only [h0, h128, h2, hlam]
            · linarith only [h127, h128, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
            · linarith only [h127, h131, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h133 | h133
              · linarith only [h127, h133, hc23, hlam, hphi, u2ehi4]
              · linarith only [h133, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · linarith only [h0, h126, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
      · rcases m.htr 0 1 5 (by decide) (by decide) with h138 | h138
        · rcases m.htr 0 2 3 (by decide) (by decide) with h139 | h139
          · linarith only [h0, h1, h139, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h141 | h141
            · linarith only [h139, h141, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h143 | h143
              · linarith only [h139, h143, hc23, hlam, hphi, u2ehi4]
              · linarith only [h143, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · linarith only [h137, h138, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h147 | h147
        · rcases m.htr 0 2 3 (by decide) (by decide) with h148 | h148
          · linarith only [h0, h1, h148, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h150 | h150
            · linarith only [h148, h150, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h152 | h152
              · linarith only [h148, h152, hc23, hlam, hphi, u2ehi4]
              · linarith only [h152, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · linarith only [h0, h147, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h156 | h156
    · rcases m.htr 0 1 4 (by decide) (by decide) with h157 | h157
      · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
            · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
              · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
                · rcases m.htr 0 3 5 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h164 | h164
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h169 | h169
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                      · linarith only [h0, h156, h165, h170, h173, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h0, h156, h168, h169, h173, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h0, h156, h168, h169, h172, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h171, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                                · linarith only [h0, h156, h162, h170, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h156, h162, h164, h166, h169, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h156, h162, h165, h168, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h167, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h156, h165, h166, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h156, h161, h162, h164, h165, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h160, h164, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h162, h163, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h186 | h186
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                            · linarith only [h156, h158, h162, h186, h190, h191, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h193 | h193
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                                · linarith only [h158, h162, h186, h190, h194, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                                      · rcases h0bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, hlam, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, h158, h186, h190, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, h158, h162, h186, h190, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, h158, h190, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, h158, h186, h190, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, h158, h162, h186, h190, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h0, h158, h190, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h156, hlam, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h159, hlam, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h162, hlam, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h158, h190, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h157, hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h160, hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h156, h188, h196, hc04, hc35, hlam, hphi, ht0b, ht5b, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h158, h190, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h158, hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h161, hlam, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h186, hlam, p199_0]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [h187, hlam, p199_1]
                                        · have p199_0 := h199c.1
                                          have p199_1 := h199c.2.1
                                          have p199_2 := h199c.2.2.1
                                          have p199_3 := h199c.2.2.2
                                          linarith only [hlam, p199_0]
                                      · linarith only [h158, h162, h186, h190, h198, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h0, h157, h193, h194, h196, h197, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                  · linarith only [h196, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                              · linarith only [h187, h189, h193, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo0]
                          · linarith only [h0, h190, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                        · linarith only [h0, h156, h188, h189, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h160, h188, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h161, h162, h186, h187, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                  · linarith only [h159, h186, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h160, h161, hc25, hlam, hphi, u2ehi3]
            · linarith only [h159, h160, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h156, h159, hlam]
        · linarith only [h157, h158, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h238 | h238
        · rcases m.htr 0 2 3 (by decide) (by decide) with h239 | h239
          · rcases m.htr 0 2 4 (by decide) (by decide) with h240 | h240
            · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 0 3 4 (by decide) (by decide) with h242 | h242
                · linarith only [h156, h157, h242, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h247 | h247
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h248 | h248
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h249 | h249
                            · linarith only [h156, h157, h242, h249, hlam]
                            · linarith only [h156, h157, h246, h249, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h156, h157, h246, h247, h248, hc25, hlam, hphi, u2ehi2]
                        · linarith only [h0, h156, h240, h246, h247, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h240, h246, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h156, h157, h245, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h239, h244, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h240, h241, hc25, hlam, hphi, u2ehi3]
            · linarith only [h239, h240, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h156, h239, hlam]
        · linarith only [h156, h238, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h261 | h261
      · rcases m.htr 0 1 5 (by decide) (by decide) with h262 | h262
        · rcases m.htr 0 2 3 (by decide) (by decide) with h263 | h263
          · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
            · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
              · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
                · rcases m.htr 0 3 5 (by decide) (by decide) with h267 | h267
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h268 | h268
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                                      · rcases h0bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h0, hlam, p278_1]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h156, hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h156, h261, h269, h271, h273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h156, h262, h269, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p278_1]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h0, h156, h261, h271, h273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h0, h261, h271, h273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h0, h262, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h261, h271, h273, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h263, hlam, p278_1]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h156, h261, h269, h271, h273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h156, h262, h269, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h261, hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h264, hlam, p278_0]
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
                                          linarith only [h262, h271, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi4]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h262, hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h265, hlam, p278_1]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h267, hlam, p278_0]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [h268, hlam, p278_1]
                                        · have p278_0 := h278c.1
                                          have p278_1 := h278c.2.1
                                          have p278_2 := h278c.2.2.1
                                          have p278_3 := h278c.2.2.2
                                          linarith only [hlam, p278_0]
                                      · linarith only [h156, h261, h269, h273, h277, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h156, h261, h269, h273, h276, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h275, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                                · linarith only [h156, h261, h269, h272, h274, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h156, h261, h268, h269, h270, h273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h156, h261, h270, h272, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h156, h261, h269, h270, h271, hc25, hlam, hphi, u2ehi3]
                        · linarith only [h156, h262, h265, h269, h270, hc24, hlam, hphi, u2ehi4]
                      · linarith only [h0, h261, h263, h265, h268, h269, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h264, h268, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h156, h261, h267, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h156, h261, h266, hlam]
              · linarith only [h265, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
            · linarith only [h263, h264, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h318 | h318
            · linarith only [h263, h318, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h261, h318, hlam]
        · linarith only [h261, h262, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h322 | h322
        · rcases m.htr 0 2 3 (by decide) (by decide) with h323 | h323
          · rcases m.htr 0 2 4 (by decide) (by decide) with h324 | h324
            · rcases m.htr 0 2 5 (by decide) (by decide) with h325 | h325
              · rcases m.htr 0 3 4 (by decide) (by decide) with h326 | h326
                · rcases m.htr 0 3 5 (by decide) (by decide) with h327 | h327
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h328 | h328
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h330 | h330
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h331 | h331
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h335 | h335
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                                      · rcases h0bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, hlam, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h156, hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h261, hlam, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h261, h332, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, h261, h322, h326, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, h261, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h322, h331, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h323, hlam, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, h261, h322, h323, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, h322, h323, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h322, h331, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h324, hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h326, hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h0, h322, h323, h326, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h322, hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h325, hlam, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h327, hlam, p338_0]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [h328, hlam, p338_1]
                                        · have p338_0 := h338c.1
                                          have p338_1 := h338c.2.1
                                          have p338_2 := h338c.2.2.1
                                          have p338_3 := h338c.2.2.2
                                          linarith only [hlam, p338_0]
                                      · rcases h0bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h0, hlam, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h156, hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h261, hlam, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h322, h331, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h0, h156, hc01, hc12, hlam, hphi, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h0, h261, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h0, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h322, h331, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h323, hlam, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h156, h261, h322, h329, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h156, h322, h329, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h322, h331, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h324, hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h326, hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h261, h322, h329, h331, h332, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p364_1, u2ehi4]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h322, hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h325, hlam, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h327, hlam, p364_0]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [h328, hlam, p364_1]
                                        · have p364_0 := h364c.1
                                          have p364_1 := h364c.2.1
                                          have p364_2 := h364c.2.2.1
                                          have p364_3 := h364c.2.2.2
                                          linarith only [hlam, p364_0]
                                    · linarith only [h336, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                                  · linarith only [h335, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h392 | h392
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h393 | h393
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h394 | h394
                                      · rcases h0bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h156, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h261, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h322, h331, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h156, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h261, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h0, h322, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h322, h331, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h323, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h156, h261, h322, h329, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h156, h322, h329, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h322, h331, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h324, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h326, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h261, h322, h329, h331, h332, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p395_1, u2ehi4]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h322, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h325, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h327, hlam, p395_0]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [h328, hlam, p395_1]
                                        · have p395_0 := h395c.1
                                          have p395_1 := h395c.2.1
                                          have p395_2 := h395c.2.2.1
                                          have p395_3 := h395c.2.2.2
                                          linarith only [hlam, p395_0]
                                      · linarith only [h334, h392, h394, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h322, h333, h334, h392, h393, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo0]
                                  · linarith only [h392, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                              · linarith only [h261, h333, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                            · linarith only [h156, h322, h331, h332, hc34, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h0, h331, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                        · linarith only [h0, h322, h325, h330, hc24, hlam, hphi, u2ehi4]
                      · linarith only [h0, h322, h323, h325, h329, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h261, h322, h325, h328, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                  · linarith only [h156, h322, h325, h327, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h431 | h431
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h432 | h432
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
                          · linarith only [h156, h322, h326, h435, hc34, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h0, h435, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                        · linarith only [h156, h322, h324, h433, h434, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h322, h325, h433, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h326, h431, h432, hc35, hlam, hphi, u5elo4]
                  · linarith only [h156, h322, h325, h431, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo3]
              · linarith only [h323, h325, hc25, hlam, hphi, u2ehi2]
            · linarith only [h323, h324, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h444 | h444
            · linarith only [h323, h444, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h446 | h446
              · linarith only [h323, h446, hc23, hlam, hphi, u2ehi4]
              · linarith only [h446, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h449 | h449
          · rcases m.htr 0 2 4 (by decide) (by decide) with h450 | h450
            · rcases m.htr 0 2 5 (by decide) (by decide) with h451 | h451
              · rcases m.htr 0 3 4 (by decide) (by decide) with h452 | h452
                · rcases m.htr 0 3 5 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h457 | h457
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h458 | h458
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h459 | h459
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h462 | h462
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h463 | h463
                                      · rcases h0bigk with h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, hlam, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h156, hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h261, hlam, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h322, hlam, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, h449, h460, h463, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p464_1, u2ehi3]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p464_1, u2ehi4]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h156, hc01, hc13, hlam, hphi, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h449, hlam, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, h449, h451, h454, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p464_1, u2ehi4]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, h449, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p464_1, u2ehi4]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h261, hc01, hc14, hlam, hphi, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h450, hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h452, hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h0, h449, h451, h452, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p464_1, u2ehi4]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p464_1, u5elo0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h451, hlam, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h453, hlam, p464_0]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [h454, hlam, p464_1]
                                        · have p464_0 := h464c.1
                                          have p464_1 := h464c.2.1
                                          have p464_2 := h464c.2.2.1
                                          have p464_3 := h464c.2.2.2
                                          linarith only [hlam, p464_0]
                                      · rcases h0bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h0, hlam, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h156, hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h261, hlam, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h322, hlam, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h0, h156, hc01, hc12, hlam, hphi, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h0, h261, hc01, hc12, hlam, hphi, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h0, h322, hc01, hc12, hlam, hphi, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h156, h455, hc01, hc12, hlam, hphi, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h449, hlam, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h156, h450, h455, h462, h463, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h156, h451, h455, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p490_1, u2ehi4]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h261, h455, h458, hc01, hc12, hlam, hphi, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h450, hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h452, hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h261, h451, h455, h458, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p490_1, u2ehi4]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p490_1, u5elo0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h451, hlam, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h453, hlam, p490_0]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [h454, hlam, p490_1]
                                        · have p490_0 := h490c.1
                                          have p490_1 := h490c.2.1
                                          have p490_2 := h490c.2.2.1
                                          have p490_3 := h490c.2.2.2
                                          linarith only [hlam, p490_0]
                                    · linarith only [h322, h454, h462, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo1]
                                  · linarith only [h461, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h519 | h519
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                                      · rcases h0bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, hlam, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h156, hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h261, hlam, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h322, hlam, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, h452, h460, h518, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u2ehi4]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, h261, hc01, hc12, hlam, hphi, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, h322, hc01, hc12, hlam, hphi, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h156, hc01, hc13, hlam, hphi, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h449, hlam, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, h449, h450, h460, h518, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u2ehi4]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, h449, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u2ehi4]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h261, h458, hc01, hc13, hlam, hphi, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h450, hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h452, hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h0, h449, h451, h452, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u2ehi4]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p521_1, u5elo0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h451, hlam, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h453, hlam, p521_0]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [h454, hlam, p521_1]
                                        · have p521_0 := h521c.1
                                          have p521_1 := h521c.2.1
                                          have p521_2 := h521c.2.2.1
                                          have p521_3 := h521c.2.2.2
                                          linarith only [hlam, p521_0]
                                      · linarith only [h460, h518, h520, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h322, h454, h460, h518, h519, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo1]
                                  · linarith only [h518, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                              · linarith only [h261, h322, h454, h459, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                            · linarith only [h0, h156, h449, h452, h458, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h457, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                        · linarith only [h0, h449, h456, hc24, hlam, hphi, u2ehi2]
                      · linarith only [h0, h449, h455, hlam]
                    · linarith only [h450, h454, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                  · linarith only [h452, h453, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h557 | h557
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h558 | h558
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h559 | h559
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h561 | h561
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h563 | h563
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                                · linarith only [h449, h451, h452, h557, h564, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h566 | h566
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h567 | h567
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h568 | h568
                                      · rcases h0bigk with h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h0, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h156, hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h261, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h322, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h0, h451, h557, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p569_1, u2ehi4]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h0, h451, h452, h557, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p569_1, u2ehi4]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h0, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p569_1, u2ehi4]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h452, h562, hc01, hc13, hlam, hphi, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h449, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h452, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h452, h562, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h261, hc01, hc14, hlam, hphi, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h450, hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h452, h562, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h451, h452, h562, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p569_1, u2ehi4]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p569_1, u5elo0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h451, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h557, hlam, p569_0]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [h558, hlam, p569_1]
                                        · have p569_0 := h569c.1
                                          have p569_1 := h569c.2.1
                                          have p569_2 := h569c.2.2.1
                                          have p569_3 := h569c.2.2.2
                                          linarith only [hlam, p569_0]
                                      · linarith only [h451, h452, h557, h568, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h452, h557, h558, h559, h562, h564, h566, h567, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h566, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                              · linarith only [h261, h452, h557, h558, h559, h562, h563, hc01, hc12, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h599 | h599
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                                · linarith only [h156, h449, h562, h600, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h602 | h602
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
                                      · rcases h0bigk with h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h0, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h156, hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h261, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h322, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h0, hc01, hc12, hlam, hphi, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h0, h451, h557, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p605_1, u2ehi4]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h0, h261, hc01, hc12, hlam, hphi, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h0, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p605_1, u2ehi4]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h156, hc01, hc13, hlam, hphi, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h449, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h452, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h451, h452, hc34, hlam, hphi, ht23, p605_1, u2ehi4]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h261, h562, hc01, hc34, hlam, hphi, ht12, ht23, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h450, hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h261, h562, hc03, hc34, hlam, hphi, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h261, h451, h562, hc34, hlam, hphi, ht23, p605_1, u2ehi4]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p605_1, u5elo0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h451, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h557, hlam, p605_0]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [h558, hlam, p605_1]
                                        · have p605_0 := h605c.1
                                          have p605_1 := h605c.2.1
                                          have p605_2 := h605c.2.2.1
                                          have p605_3 := h605c.2.2.2
                                          linarith only [hlam, p605_0]
                                      · linarith only [h562, h604, hc13, hlam, hphi, ht34, ht45, u5elo4]
                                    · linarith only [h156, h557, h558, h562, h603, hc34, hlam, hphi, ht23, u2ehi3]
                                  · linarith only [h156, h557, h562, h602, hc23, hc34, hlam, hphi]
                              · linarith only [h261, h322, h558, h599, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                          · linarith only [h0, h451, h561, hlam]
                        · linarith only [h0, h451, h560, hc24, hlam, hphi, u2ehi4]
                      · linarith only [h0, h451, h559, hc23, hlam, hphi, u2ehi4]
                    · linarith only [h452, h557, h558, hc35, hlam, hphi, u5elo4]
                  · linarith only [h449, h557, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h451, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
            · linarith only [h449, h450, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h642 | h642
            · linarith only [h449, h642, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h644 | h644
              · linarith only [h449, h644, hc23, hlam, hphi, u2ehi4]
              · linarith only [h644, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

end R2N4
