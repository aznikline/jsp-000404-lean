import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h5, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                    · linarith only [h3, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h2, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h3, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h1, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
              · linarith only [h15, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h1, h15, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h18, h22, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                    · linarith only [h20, h22, hc23, hlam, hphi, u3elo1]
                  · linarith only [h2, h21, hc23, hlam, hphi, u3elo0]
                · linarith only [h20, h3, hc13, hlam, hphi, u3elo0]
              · linarith only [h1, h19, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
              · linarith only [h18, h28, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h1, h28, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
          · linarith only [h2, h3, h31, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
            · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
              · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                · linarith only [h3, h35, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h33, h35, h38, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                      · linarith only [h0, h31, h33, h35, h37, h40, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                        · linarith only [h2, h31, h42, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h0emin with h44 | h44 | h44 | h44 | h44
                          · rcases h5bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h1, h33, h35, h37, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p45_1, u2elo0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h1, h37, h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p45_1, u2elo0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h3, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h31, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, h37, h38, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h35, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, h3, h42, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h1, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h34, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h38, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h40, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo4, u5ehi1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h34, h37, h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p45_1, u3elo4]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h37, h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p45_1, u3elo4]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h42, hlam, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h0, h34, h37, h38, hc34, hc45, hlam, hphi, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h34, h37, h38, hc34, hc45, hlam, hphi, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h37, h38, hc34, hc45, hlam, hphi, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [h2, h3, hc34, hc45, hlam, hphi, p45_1]
                            · have p45_0 := h45c.1
                              have p45_1 := h45c.2.1
                              have p45_2 := h45c.2.2.1
                              have p45_3 := h45c.2.2.2
                              linarith only [hlam, p45_0]
                          · linarith only [h44, hlam, ht01, ht12, u2elo0]
                          · linarith only [h44, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h2, h44, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h1, h44, hlam, ht01, ht12, u2elo0]
                  · linarith only [h2, h3, h37, hc23, hlam, hphi, u3elo4]
              · linarith only [h1, h34, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
              · linarith only [h33, h77, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h1, h77, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
        · linarith only [h2, h80, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
          · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
            · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                · linarith only [h80, h85, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                  · linarith only [h2, h83, h85, h87, hc03, hlam, hphi, u3elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h83, h85, h89, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                        · rcases h0emin with h93 | h93 | h93 | h93 | h93
                          · rcases h5bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p94_1, u2elo0, u5ehi1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p94_1, u2elo0, u5ehi2]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h80, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h2, h82, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo3, u5ehi4]
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
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p94_1, u5ehi2]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h85, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h0, h2, h82, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo3, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h1, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h84, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h89, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p94_1, u2elo4, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h92, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo3, u5ehi0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h84, h92, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo3, u5ehi2]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h92, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo3, u5ehi2]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h92, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p94_1, u3elo3, u5ehi4]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h82, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h84, h91, hlam, p94_1]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h91, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [h92, hlam, p94_0]
                            · have p94_0 := h94c.1
                              have p94_1 := h94c.2.1
                              have p94_2 := h94c.2.2.1
                              have p94_3 := h94c.2.2.2
                              linarith only [hlam, p94_0]
                          · linarith only [h93, hlam, ht01, ht12, u2elo0]
                          · linarith only [h93, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h2, h93, hlam, ht01, ht12, ht23, u3elo3]
                          · linarith only [h1, h93, hlam, ht01, ht12, u2elo0]
                        · linarith only [h2, h91, h92, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h2, h82, h87, h91, hc23, hlam, hphi, u3elo3]
              · linarith only [h1, h84, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
              · linarith only [h127, h83, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h1, h127, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
            · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
              · rcases m.htr 1 3 5 (by decide) (by decide) with h132 | h132
                · linarith only [h132, h80, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                  · linarith only [h130, h132, h134, h2, hc03, hlam, hphi, u3elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
                    · linarith only [h130, h136, h80, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h134, h138, h2, h82, hc03, hlam, hphi, u3elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h140, h2, h82, hc03, hlam, hphi, u3elo3]
                        · rcases h0emin with h142 | h142 | h142 | h142 | h142
                          · rcases h5bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h1, h131, hlam, hphi, ht01, ht0b, ht12, ht5b, p143_1, u2elo0, u5ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p143_1, u2elo0, u5ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h80, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h82, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p143_1, u5ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h132, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h0, h140, h80, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p143_1, u3elo4]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h1, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h131, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h136, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h138, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p143_1, u3elo4, u5ehi0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h131, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p143_1, u3elo4, u5ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p143_1, u3elo4, u5ehi2]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h140, hlam, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              rcases p143_3 (m.d 0 5) (by simp) with h164 | h164
                              · linarith only [h164, h82, hlam]
                              · rcases p143_3 (m.d 1 5) (by simp) with h166 | h166
                                · linarith only [h0, h166, hlam, p143_1]
                                · rcases p143_3 (m.d 2 5) (by simp) with h168 | h168
                                  · linarith only [h138, h168, hlam]
                                  · rcases p143_3 (m.d 3 5) (by simp) with h170 | h170
                                    · linarith only [h140, h170, hlam]
                                    · linarith only [h170, h80, hlam]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              rcases p143_3 (m.d 0 5) (by simp) with h173 | h173
                              · linarith only [h173, h82, hlam]
                              · linarith only [h0, h173, hlam]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              rcases p143_3 (m.d 0 5) (by simp) with h176 | h176
                              · linarith only [h176, h82, hlam]
                              · linarith only [h1, h176, hlam]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [h80, hc03, hc45, hlam, hphi, ht34, p143_1]
                            · have p143_0 := h143c.1
                              have p143_1 := h143c.2.1
                              have p143_2 := h143c.2.2.1
                              have p143_3 := h143c.2.2.2
                              linarith only [hlam, p143_0]
                          · linarith only [h142, hlam, ht01, ht12, u2elo0]
                          · linarith only [h142, h2, hlam, ht01, ht12, ht23, u3elo3]
                          · linarith only [h142, h2, hlam, ht01, ht12, ht23, u3elo3]
                          · linarith only [h1, h142, hlam, ht01, ht12, u2elo0]
              · linarith only [h1, h131, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
              · linarith only [h130, h186, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h1, h186, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
      · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
        · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
          · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
            · rcases m.htr 1 2 5 (by decide) (by decide) with h193 | h193
              · linarith only [h1, h193, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h195 | h195
                · linarith only [h192, h193, h195, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · linarith only [h190, h195, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
              · linarith only [h192, h198, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h189, h204, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                        · rcases h0emin with h206 | h206 | h206 | h206 | h206
                          · rcases h5bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h1, h201, h203, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo2, u5ehi1]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h1, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h1, h201, h203, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo2, u5ehi3]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h1, h201, h203, h204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p207_1, u3elo2]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h0, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h198, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p207_1, u5ehi3]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h0, h1, h201, h203, h204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p207_1, u3elo2]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h201, h203, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo2, u5ehi0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h201, h203, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo2, u5ehi1]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h201, h203, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo2, u5ehi3]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h201, h203, h204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p207_1, u3elo2]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h190, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h200, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h202, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h204, hlam, p207_1]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h191, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h191, h200, hc04, hlam, hphi, ht0b, ht5b, p207_1, u5ehi3]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h203, hlam, p207_0]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [h189, h191, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p207_1, u3elo0, u5ehi3]
                            · have p207_0 := h207c.1
                              have p207_1 := h207c.2.1
                              have p207_2 := h207c.2.2.1
                              have p207_3 := h207c.2.2.2
                              linarith only [hlam, p207_0]
                          · linarith only [h206, hlam, ht01, ht12, u2elo0]
                          · linarith only [h206, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h189, h206, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h1, h201, h203, h206, hlam, ht01, ht12, ht23, u3elo2]
                      · linarith only [h1, h189, h191, h203, hc02, hlam, hphi, ht23, u3elo0]
                    · linarith only [h200, h202, hc23, hlam, hphi, u3elo1]
                  · linarith only [h192, h200, h201, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h190, h200, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h241 | h241
            · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
              · linarith only [h1, h242, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                · linarith only [h241, h242, h244, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · linarith only [h190, h244, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
              · linarith only [h241, h247, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h251 | h251
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h252 | h252
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h253 | h253
                        · linarith only [h189, h191, h253, hlam]
                        · rcases h0emin with h255 | h255 | h255 | h255 | h255
                          · rcases h5bigk with h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c | h256c
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h191, h247, h250, h252, hc12, hlam, hphi, ht23, p256_1, u3elo2]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h1, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h191, h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi3]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h191, hlam, p256_1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h0, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h247, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p256_1, u5ehi3]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h0, h191, hlam, p256_1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi3]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h189, h191, h250, h252, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p256_1, u3elo2]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h190, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h249, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h251, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h253, hlam, p256_1]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h0, h249, h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi3]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h249, h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi3]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h252, hlam, p256_0]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [h250, h252, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p256_1, u3elo2, u5ehi3]
                            · have p256_0 := h256c.1
                              have p256_1 := h256c.2.1
                              have p256_2 := h256c.2.2.1
                              have p256_3 := h256c.2.2.2
                              linarith only [hlam, p256_0]
                          · linarith only [h255, hlam, ht01, ht12, u2elo0]
                          · linarith only [h255, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h189, h255, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h1, h250, h252, h255, hlam, ht01, ht12, ht23, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h286 | h286
                        · linarith only [h189, h191, h286, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h0emin with h288 | h288 | h288 | h288 | h288
                          · rcases h5bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, h249, hlam, hphi, ht01, ht0b, ht12, ht5b, p289_1, u2elo4, u5ehi3]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h190, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo0, u5ehi3]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h191, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h0, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h247, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p289_1, u5ehi3]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h0, h1, h252, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h251, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo2, u5ehi0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h251, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo2, u5ehi1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h251, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p289_1, u3elo2, u5ehi3]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h252, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h190, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h249, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h251, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h286, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              rcases p289_3 (m.d 0 5) (by simp) with h310 | h310
                              · linarith only [h191, h310, hlam]
                              · rcases p289_3 (m.d 1 5) (by simp) with h312 | h312
                                · linarith only [h0, h312, hlam, p289_1]
                                · rcases p289_3 (m.d 2 5) (by simp) with h314 | h314
                                  · linarith only [h252, h314, hlam]
                                  · linarith only [h1, h314, hlam]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              rcases p289_3 (m.d 0 5) (by simp) with h317 | h317
                              · linarith only [h191, h317, hlam]
                              · linarith only [h0, h317, hlam]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              rcases p289_3 (m.d 0 5) (by simp) with h321 | h321
                              · linarith only [h191, h321, hlam]
                              · linarith only [h190, h321, hlam]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                          · linarith only [h1, h288, hlam, ht01, ht12, u2elo4]
                          · linarith only [h288, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h189, h288, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h1, h288, hlam, ht01, ht12, u2elo4]
                    · linarith only [h249, h251, hc23, hlam, hphi, u3elo1]
                  · linarith only [h241, h249, h250, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h190, h249, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
          · linarith only [h189, h190, h332, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
            · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
              · linarith only [h1, h335, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                · linarith only [h190, h337, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                  · linarith only [h334, h335, h339, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h189, h339, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
              · linarith only [h334, h342, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h344 | h344
                · linarith only [h190, h344, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                    · linarith only [h334, h344, h347, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h334, h347, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h334, h346, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h351 | h351
        · linarith only [h189, h351, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
          · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
            · rcases m.htr 1 2 5 (by decide) (by decide) with h355 | h355
              · linarith only [h1, h355, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
                · linarith only [h351, h357, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                  · linarith only [h189, h354, h355, h359, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h361 | h361
                    · linarith only [h354, h355, h357, h361, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h354, h355, h361, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
              · linarith only [h354, h364, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h366 | h366
                · linarith only [h351, h366, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                  · linarith only [h189, h353, h368, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · linarith only [h354, h368, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
            · rcases m.htr 1 2 5 (by decide) (by decide) with h372 | h372
              · linarith only [h1, h372, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                · linarith only [h351, h374, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                  · linarith only [h189, h371, h376, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
                    · linarith only [h351, h353, h371, h372, h378, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h371, h372, h378, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
              · linarith only [h371, h381, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h383 | h383
                · linarith only [h351, h383, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                  · linarith only [h189, h385, hc03, hlam, hphi, u3elo2]
                  · linarith only [h371, h385, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h388 | h388
    · rcases m.htr 0 3 4 (by decide) (by decide) with h389 | h389
      · rcases m.htr 0 3 5 (by decide) (by decide) with h390 | h390
        · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
          · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
            · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
              · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                    · linarith only [h392, h396, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                    · linarith only [h394, h396, hc23, hlam, hphi, u3elo1]
                  · linarith only [h389, h395, hc23, hlam, hphi, u3elo0]
                · linarith only [h390, h394, hc13, hlam, hphi, u3elo0]
              · linarith only [h388, h393, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
              · linarith only [h392, h402, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h388, h402, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
            · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
              · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                    · linarith only [h405, h409, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                    · linarith only [h390, h409, hc23, hlam, hphi, u3elo0]
                  · linarith only [h389, h408, hc23, hlam, hphi, u3elo0]
                · linarith only [h390, h407, hc13, hlam, hphi, u3elo0]
              · linarith only [h388, h406, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h415 | h415
              · linarith only [h405, h415, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h388, h415, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
          · linarith only [h389, h390, h418, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
            · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
              · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                · linarith only [h390, h422, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h425 | h425
                    · linarith only [h420, h422, h425, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                      · linarith only [h418, h420, h422, h424, h427, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h429 | h429
                        · linarith only [h389, h418, h429, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi0]
                        · rcases h0emin with h431 | h431 | h431 | h431 | h431
                          · linarith only [h0, h431, hc15, hlam, ht01]
                          · linarith only [h431, hlam, ht01, ht12, u2elo0]
                          · linarith only [h431, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h389, h431, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h388, h431, hlam, ht01, ht12, u2elo0]
                  · linarith only [h389, h390, h424, hc23, hlam, hphi, u3elo4]
              · linarith only [h388, h421, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h439 | h439
              · linarith only [h420, h439, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h388, h439, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h442 | h442
        · linarith only [h389, h442, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h444 | h444
          · rcases m.htr 1 2 3 (by decide) (by decide) with h445 | h445
            · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
              · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
                · linarith only [h442, h447, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                  · linarith only [h389, h445, h447, h449, hc03, hlam, hphi, u3elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                    · linarith only [h445, h447, h451, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                        · rcases h0emin with h455 | h455 | h455 | h455 | h455
                          · linarith only [h0, h447, h454, h455, hlam, ht01, ht12, ht23, u3elo3]
                          · linarith only [h455, hlam, ht01, ht12, u2elo0]
                          · linarith only [h455, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h389, h455, hlam, ht01, ht12, ht23, u3elo3]
                          · linarith only [h0, h447, h454, h455, hlam, ht01, ht12, ht23, u3elo3]
                        · linarith only [h389, h453, h454, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h389, h444, h449, h453, hc23, hlam, hphi, u3elo3]
              · linarith only [h388, h446, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h464 | h464
              · linarith only [h445, h464, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h388, h464, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
            · rcases m.htr 1 2 5 (by decide) (by decide) with h468 | h468
              · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                · linarith only [h442, h469, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                  · linarith only [h389, h471, hc03, hlam, hphi, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                    · linarith only [h467, h469, h473, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h475 | h475
                      · linarith only [h389, h444, h471, h475, hc03, hlam, hphi, u3elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h477 | h477
                        · linarith only [h389, h444, h477, hc03, hlam, hphi, u3elo3]
                        · rcases h0emin with h479 | h479 | h479 | h479 | h479
                          · linarith only [h0, h479, hc15, hlam, ht01]
                          · linarith only [h479, hlam, ht01, ht12, u2elo0]
                          · linarith only [h479, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h389, h477, h479, hc45, hlam, ht01, ht12, ht23, ht34]
                          · linarith only [h388, h479, hlam, ht01, ht12, u2elo0]
              · linarith only [h388, h468, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
              · linarith only [h467, h486, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · linarith only [h388, h486, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h489 | h489
      · rcases m.htr 0 3 5 (by decide) (by decide) with h490 | h490
        · rcases m.htr 0 4 5 (by decide) (by decide) with h491 | h491
          · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
            · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
              · linarith only [h388, h493, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                · linarith only [h492, h493, h495, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · linarith only [h490, h495, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
              · linarith only [h492, h498, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h500 | h500
                · rcases m.htr 2 3 4 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h503 | h503
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
                        · linarith only [h489, h504, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                        · rcases h0emin with h506 | h506 | h506 | h506 | h506
                          · linarith only [h0, h498, h501, h503, h506, hlam, ht01, ht12, ht23, u3elo2]
                          · linarith only [h506, hlam, ht01, ht12, u2elo0]
                          · linarith only [h506, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h489, h506, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h0, h498, h501, h503, h506, hlam, ht01, ht12, ht23, u3elo2]
                      · linarith only [h0, h489, h491, h498, h503, hc01, hlam, hphi, ht12, ht23, u3elo0]
                    · linarith only [h490, h492, h502, hc13, hlam, hphi, u3elo0]
                  · linarith only [h492, h500, h501, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h490, h500, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h516 | h516
            · rcases m.htr 1 2 5 (by decide) (by decide) with h517 | h517
              · linarith only [h388, h517, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
                · linarith only [h516, h517, h519, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · linarith only [h490, h519, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h522 | h522
              · linarith only [h388, h522, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 2 3 4 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h526 | h526
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h528 | h528
                        · linarith only [h489, h491, h528, hlam]
                        · rcases h0emin with h530 | h530 | h530 | h530 | h530
                          · linarith only [h0, h530, hc15, hlam, ht01]
                          · linarith only [h530, hlam, ht01, ht12, u2elo0]
                          · linarith only [h530, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h491, h525, h527, h530, hlam, ht01, ht12, ht23, u3elo2]
                          · linarith only [h491, h525, h527, h530, hlam, ht01, ht12, ht23, u3elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                        · linarith only [h489, h527, h536, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h0emin with h538 | h538 | h538 | h538 | h538
                          · linarith only [h0, h538, hc15, hlam, ht01]
                          · linarith only [h388, h538, hlam, ht01, ht12, u2elo4]
                          · linarith only [h538, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h489, h538, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h388, h538, hlam, ht01, ht12, u2elo4]
                    · linarith only [h516, h524, h526, hlam]
                  · linarith only [h0, h516, h524, h525, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h490, h524, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
          · linarith only [h489, h490, h547, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
            · rcases m.htr 1 2 5 (by decide) (by decide) with h550 | h550
              · linarith only [h388, h550, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
                · linarith only [h490, h552, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
                  · linarith only [h549, h550, h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h489, h554, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h557 | h557
              · linarith only [h549, h557, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                · linarith only [h490, h559, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h562 | h562
                    · linarith only [h549, h559, h562, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h549, h562, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h549, h561, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h566 | h566
        · linarith only [h489, h566, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
          · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
            · rcases m.htr 1 2 5 (by decide) (by decide) with h570 | h570
              · linarith only [h388, h570, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                · linarith only [h566, h572, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h574 | h574
                  · linarith only [h489, h569, h570, h574, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                    · linarith only [h569, h570, h572, h576, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi1]
                    · linarith only [h569, h570, h576, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
              · linarith only [h569, h579, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h581 | h581
                · linarith only [h566, h581, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h583 | h583
                  · linarith only [h489, h568, h583, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                  · linarith only [h569, h583, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h586 | h586
            · rcases m.htr 1 2 5 (by decide) (by decide) with h587 | h587
              · linarith only [h388, h587, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h589 | h589
                · linarith only [h566, h589, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                  · linarith only [h586, h587, h591, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h593 | h593
                    · linarith only [h586, h587, h589, h593, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h586, h587, h593, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h596 | h596
              · linarith only [h586, h596, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
                · linarith only [h566, h598, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                  · linarith only [h489, h600, hc03, hlam, hphi, u3elo2]
                  · linarith only [h586, h600, hc12, hlam, hphi, ht23, u3elo3]

end R2N4
