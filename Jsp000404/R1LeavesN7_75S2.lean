import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_13_25_L_R_L_I_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h11, h12, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h11, h15, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                            · linarith only [h0, h17, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h11, h17, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h21, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h0, h20, h21, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h10, h20, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h5, h8, h9, hc34, hlam, hphi, ht45, u5elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h0, h2, h26, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                        · linarith only [h26, h29, h5, h6, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                          · linarith only [h26, h31, h6, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                            · rcases h3bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 3) (by simp) with h36 | h36
                                · rcases p34_3 (m.d 1 3) (by simp) with h37 | h37
                                  · linarith only [h1, h37, hlam]
                                  · rcases p34_3 (m.d 2 3) (by simp) with h39 | h39
                                    · linarith only [h2, h39, hlam]
                                    · rcases p34_3 (m.d 3 4) (by simp) with h41 | h41
                                      · linarith only [h4, h41, hlam]
                                      · linarith only [h41, h8, hlam]
                                · linarith only [h1, h36, hlam]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 3) (by simp) with h45 | h45
                                · rcases p34_3 (m.d 1 3) (by simp) with h46 | h46
                                  · linarith only [h1, h46, hlam]
                                  · linarith only [h46, h6, hlam]
                                · linarith only [h2, h45, hlam]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, h2, h28, h8, hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi9]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 3) (by simp) with h51 | h51
                                · rcases p34_3 (m.d 1 3) (by simp) with h52 | h52
                                  · linarith only [h1, h52, hlam]
                                  · rcases p34_3 (m.d 2 3) (by simp) with h54 | h54
                                    · linarith only [h2, h54, hlam]
                                    · rcases p34_3 (m.d 3 4) (by simp) with h56 | h56
                                      · linarith only [h4, h56, hlam]
                                      · linarith only [h33, h56, hlam]
                                · linarith only [h51, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h1, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h26, hc23, hc35, hlam, hphi, p34_1]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h8, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h26, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h2, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h6, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h29, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h31, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h4, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 3) (by simp) with h71 | h71
                                · rcases p34_3 (m.d 1 3) (by simp) with h72 | h72
                                  · linarith only [h72, hlam, p34_0]
                                  · rcases p34_3 (m.d 2 3) (by simp) with h74 | h74
                                    · linarith only [h29, h74, hlam]
                                    · rcases p34_3 (m.d 3 4) (by simp) with h76 | h76
                                      · rcases p34_3 (m.d 3 5) (by simp) with h77 | h77
                                        · linarith only [h33, h77, hlam]
                                        · linarith only [h26, h77, hlam]
                                      · linarith only [h76, hlam, p34_0]
                                · linarith only [h1, h71, hlam]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                rcases p34_3 (m.d 0 3) (by simp) with h82 | h82
                                · rcases p34_3 (m.d 1 3) (by simp) with h83 | h83
                                  · linarith only [h8, h83, hlam]
                                  · linarith only [h6, h83, hlam]
                                · linarith only [h2, h82, hlam]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h0, h2, h26, h4, hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi6]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h5, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p34_1, u5elo3]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h5, hc23, hlam, hphi, ht34, ht45, p34_1, u5elo0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [h33, hlam, p34_0]
                              · have p34_0 := h34c.1
                                have p34_1 := h34c.2.1
                                have p34_2 := h34c.2.2.1
                                have p34_3 := h34c.2.2.2
                                linarith only [hlam, p34_0]
                            · linarith only [h33, h6, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                        · linarith only [h6, h8, h95, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                          · linarith only [h28, h6, h8, h97, hlam, hphi, u5ehi8, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                            · rcases h3bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h28, h4, h8, h99, hlam, p100_2]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h28, h4, h6, h8, h99, hlam, p100_2]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, h2, h28, h8, h99, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 3) (by simp) with h105 | h105
                                · rcases p100_3 (m.d 1 3) (by simp) with h106 | h106
                                  · linarith only [h1, h106, hlam]
                                  · rcases p100_3 (m.d 2 3) (by simp) with h108 | h108
                                    · linarith only [h108, h2, hlam]
                                    · rcases p100_3 (m.d 3 4) (by simp) with h110 | h110
                                      · linarith only [h110, h4, hlam]
                                      · linarith only [h110, h99, hlam]
                                · linarith only [h105, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h1, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h28, h8, h99, hc23, hc34, hlam, hphi, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h8, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h26, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h2, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h6, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h95, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h97, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h4, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 3) (by simp) with h125 | h125
                                · rcases p100_3 (m.d 1 3) (by simp) with h126 | h126
                                  · linarith only [h126, hlam, p100_0]
                                  · rcases p100_3 (m.d 2 3) (by simp) with h128 | h128
                                    · linarith only [h128, h95, hlam]
                                    · rcases p100_3 (m.d 3 4) (by simp) with h130 | h130
                                      · rcases p100_3 (m.d 3 5) (by simp) with h131 | h131
                                        · linarith only [h131, h99, hlam]
                                        · linarith only [h131, h26, hlam]
                                      · linarith only [h130, hlam, p100_0]
                                · linarith only [h1, h125, hlam]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 3) (by simp) with h136 | h136
                                · rcases p100_3 (m.d 1 3) (by simp) with h137 | h137
                                  · linarith only [h137, h8, hlam]
                                  · linarith only [h137, h6, hlam]
                                · linarith only [h136, h2, hlam]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, p100_1, u5ehi8]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h5, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hc13, hlam, hphi, ht34, ht45, p100_1, u5elo3]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h5, hc23, hlam, hphi, ht34, ht45, p100_1, u5elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h99, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                            · linarith only [h6, h8, h99, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h3, h6, h7, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                · linarith only [h0, h150, h2, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                            · linarith only [h1, h152, h157, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
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
                                linarith only [h0, h152, h154, h157, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h0, h152, h154, h157, h2, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 3) (by simp) with h163 | h163
                                · rcases p159_3 (m.d 1 3) (by simp) with h164 | h164
                                  · linarith only [h1, h164, hlam]
                                  · linarith only [h152, h164, hlam]
                                · linarith only [h163, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 3) (by simp) with h168 | h168
                                · rcases p159_3 (m.d 1 3) (by simp) with h169 | h169
                                  · linarith only [h1, h169, hlam]
                                  · linarith only [h153, h169, hlam]
                                · linarith only [h168, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h1, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h6, hlam, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 3) (by simp) with h176 | h176
                                · rcases p159_3 (m.d 1 3) (by simp) with h177 | h177
                                  · rcases p159_3 (m.d 2 3) (by simp) with h178 | h178
                                    · rcases p159_3 (m.d 3 4) (by simp) with h179 | h179
                                      · linarith only [h179, hlam, p159_0]
                                      · rcases p159_3 (m.d 3 5) (by simp) with h181 | h181
                                        · linarith only [h153, h181, hlam]
                                        · linarith only [h157, h181, hlam]
                                    · linarith only [h155, h178, hlam]
                                  · linarith only [h177, hlam, p159_0]
                                · linarith only [h176, h4, hlam]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h0, h2, h6, hc01, hlam, hphi, ht0b, ht5b, p159_1, u5ehi8]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h2, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h0, h152, h154, h157, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 3) (by simp) with h191 | h191
                                · rcases p159_3 (m.d 1 3) (by simp) with h192 | h192
                                  · linarith only [h192, h6, hlam]
                                  · linarith only [h152, h192, hlam]
                                · linarith only [h191, h4, hlam]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p159_1, u5ehi8]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h4, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h152, hlam, p159_0]
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
                                linarith only [h5, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h153, hlam, p159_0]
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
                          · linarith only [h153, h156, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                        · linarith only [h0, h153, h155, h2, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h210 | h210
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                            · linarith only [h152, h154, h211, hlam]
                            · rcases h3bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h0, h153, h2, hc01, hlam, hphi, ht0b, ht5b, p213_1, u5ehi8]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h0, h153, h2, h6, hc01, hlam, hphi, ht0b, ht5b, p213_1, u5ehi8]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 3) (by simp) with h217 | h217
                                · rcases p213_3 (m.d 1 3) (by simp) with h218 | h218
                                  · linarith only [h1, h218, hlam]
                                  · linarith only [h152, h218, hlam]
                                · linarith only [h217, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 3) (by simp) with h222 | h222
                                · rcases p213_3 (m.d 1 3) (by simp) with h223 | h223
                                  · linarith only [h1, h223, hlam]
                                  · linarith only [h153, h223, hlam]
                                · linarith only [h222, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h6, hlam, p213_1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 3) (by simp) with h230 | h230
                                · rcases p213_3 (m.d 1 3) (by simp) with h231 | h231
                                  · rcases p213_3 (m.d 2 3) (by simp) with h232 | h232
                                    · rcases p213_3 (m.d 3 4) (by simp) with h233 | h233
                                      · linarith only [h233, hlam, p213_0]
                                      · rcases p213_3 (m.d 3 5) (by simp) with h235 | h235
                                        · linarith only [h153, h235, hlam]
                                        · linarith only [h211, h235, hlam]
                                    · linarith only [h209, h232, hlam]
                                  · linarith only [h231, hlam, p213_0]
                                · linarith only [h230, h4, hlam]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p213_1, u5ehi8]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h2, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h0, h152, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p213_1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 3) (by simp) with h245 | h245
                                · rcases p213_3 (m.d 1 3) (by simp) with h246 | h246
                                  · linarith only [h246, h6, hlam]
                                  · linarith only [h152, h246, hlam]
                                · linarith only [h245, h4, hlam]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p213_1, u5ehi8]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h4, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h152, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h209, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h211, hlam, p213_1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h5, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h153, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h210, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hc34, hlam, hphi, ht45, p213_1, u5elo3]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                          · linarith only [h153, h210, h6, hlam]
                        · linarith only [h0, h153, h2, h209, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · linarith only [h152, h153, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h152, h2, h264, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                        · linarith only [h0, h152, h2, h266, h267, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                          · linarith only [h0, h2, h267, h269, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h269, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                            · linarith only [h0, h2, h266, h272, h274, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h152, h274, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h152, h272, h273, h6, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                          · linarith only [h264, h272, h278, hc13, hc34, hlam, hphi]
                          · linarith only [h278, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h282 | h282
            · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
              · rcases m.htr 1 2 5 (by decide) (by decide) with h284 | h284
                · rcases m.htr 1 3 4 (by decide) (by decide) with h285 | h285
                  · linarith only [h282, h285, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h287 | h287
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h288 | h288
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                        · linarith only [h1, h283, h287, h289, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                          · linarith only [h0, h283, h291, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h1, h287, h291, h4, hc23, hc34, hlam, hphi]
                      · linarith only [h285, h287, h288, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h282, h287, h4, hc13, hc34, hlam, hphi]
                · linarith only [h283, h284, h3, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h297 | h297
                · linarith only [h0, h2, h283, h297, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h299 | h299
                  · linarith only [h2, h283, h299, h4, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h301 | h301
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h302 | h302
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                        · linarith only [h2, h303, h4, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h305 | h305
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                            · rcases h3bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h301, h306, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h283, h301, h306, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h4, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h306, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h283, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h299, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, h306, hc01, hlam, hphi, ht0b, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, h4, hc13, hc34, hlam, hphi, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h303, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, h306, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p307_1, u0ehi2]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h301, h306, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h283, h301, h306, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p307_1, u5ehi9]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 3) (by simp) with h327 | h327
                                · linarith only [h327, h4, hlam]
                                · linarith only [h282, h327, hlam]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h282, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h301, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h305, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h306, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                            · linarith only [h2, h283, h301, h306, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h283, h301, h305, hlam]
                      · linarith only [h299, h301, h302, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h282, h301, h4, hc13, hc34, hlam, hphi]
            · linarith only [h282, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h341 | h341
        · rcases m.htr 0 3 4 (by decide) (by decide) with h342 | h342
          · rcases m.htr 0 3 5 (by decide) (by decide) with h343 | h343
            · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
              · linarith only [h2, h341, h344, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h351 | h351
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                            · linarith only [h1, h347, h352, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h2, h344, h346, h351, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p354_1, u5ehi8]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h2, hlam, p354_1]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                rcases p354_3 (m.d 0 3) (by simp) with h358 | h358
                                · rcases p354_3 (m.d 1 3) (by simp) with h359 | h359
                                  · linarith only [h1, h359, hlam]
                                  · linarith only [h347, h359, hlam]
                                · linarith only [h358, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                rcases p354_3 (m.d 0 3) (by simp) with h363 | h363
                                · rcases p354_3 (m.d 1 3) (by simp) with h364 | h364
                                  · linarith only [h1, h364, hlam]
                                  · linarith only [h348, h364, hlam]
                                · linarith only [h363, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h1, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h344, hlam, p354_1]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                rcases p354_3 (m.d 0 3) (by simp) with h371 | h371
                                · rcases p354_3 (m.d 1 3) (by simp) with h372 | h372
                                  · rcases p354_3 (m.d 2 3) (by simp) with h373 | h373
                                    · rcases p354_3 (m.d 3 4) (by simp) with h374 | h374
                                      · linarith only [h374, hlam, p354_0]
                                      · rcases p354_3 (m.d 3 5) (by simp) with h376 | h376
                                        · linarith only [h348, h376, hlam]
                                        · linarith only [h352, h376, hlam]
                                    · linarith only [h350, h373, hlam]
                                  · linarith only [h372, hlam, p354_0]
                                · linarith only [h342, h371, hlam]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p354_1, u5ehi8]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p354_1, u0ehi2]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h344, h346, h351, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p354_1, u5ehi8]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                rcases p354_3 (m.d 0 3) (by simp) with h386 | h386
                                · linarith only [h2, h386, hlam]
                                · linarith only [h342, h386, hlam]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                rcases p354_3 (m.d 0 3) (by simp) with h389 | h389
                                · linarith only [h2, h389, hlam]
                                · linarith only [h343, h389, hlam]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h342, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h347, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h350, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h352, hlam, p354_1]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h343, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h348, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h351, hlam, p354_0]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [h0, h2, h346, h351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p354_1]
                              · have p354_0 := h354c.1
                                have p354_1 := h354c.2.1
                                have p354_2 := h354c.2.2.1
                                have p354_3 := h354c.2.2.2
                                linarith only [hlam, p354_0]
                          · linarith only [h2, h348, h351, hc13, hlam, hphi, ht01, u0ehi1]
                        · linarith only [h0, h1, h2, h346, h347, h350, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h406 | h406
                            · linarith only [h347, h349, h406, hlam]
                            · rcases h3bigk with h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c | h408c
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h2, h344, h346, h405, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p408_1, u5ehi8]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h2, hlam, p408_1]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                rcases p408_3 (m.d 0 3) (by simp) with h412 | h412
                                · rcases p408_3 (m.d 1 3) (by simp) with h413 | h413
                                  · linarith only [h1, h413, hlam]
                                  · linarith only [h347, h413, hlam]
                                · linarith only [h412, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                rcases p408_3 (m.d 0 3) (by simp) with h417 | h417
                                · rcases p408_3 (m.d 1 3) (by simp) with h418 | h418
                                  · linarith only [h1, h418, hlam]
                                  · linarith only [h348, h418, hlam]
                                · linarith only [h417, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h1, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h344, hlam, p408_1]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                rcases p408_3 (m.d 0 3) (by simp) with h425 | h425
                                · rcases p408_3 (m.d 1 3) (by simp) with h426 | h426
                                  · rcases p408_3 (m.d 2 3) (by simp) with h427 | h427
                                    · rcases p408_3 (m.d 3 4) (by simp) with h428 | h428
                                      · linarith only [h428, hlam, p408_0]
                                      · rcases p408_3 (m.d 3 5) (by simp) with h430 | h430
                                        · linarith only [h348, h430, hlam]
                                        · linarith only [h406, h430, hlam]
                                    · linarith only [h404, h427, hlam]
                                  · linarith only [h426, hlam, p408_0]
                                · linarith only [h342, h425, hlam]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p408_1, u5ehi8]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p408_1, u0ehi2]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h344, h346, h405, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p408_1, u5ehi8]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                rcases p408_3 (m.d 0 3) (by simp) with h440 | h440
                                · linarith only [h2, h440, hlam]
                                · linarith only [h342, h440, hlam]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                rcases p408_3 (m.d 0 3) (by simp) with h443 | h443
                                · linarith only [h2, h443, hlam]
                                · linarith only [h343, h443, hlam]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h342, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h347, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h404, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h406, hlam, p408_1]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h343, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h348, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h405, hlam, p408_0]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [h405, hc34, hlam, hphi, ht45, p408_1, u5elo2]
                              · have p408_0 := h408c.1
                                have p408_1 := h408c.2.1
                                have p408_2 := h408c.2.2.1
                                have p408_3 := h408c.2.2.2
                                linarith only [hlam, p408_0]
                          · linarith only [h0, h2, h346, h348, h405, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                        · linarith only [h0, h2, h346, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h347, h348, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h342, h344, h346, h347, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h2, h341, h346, hc12, hc23, hlam, hphi]
            · linarith only [h343, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h462 | h462
            · rcases m.htr 1 2 3 (by decide) (by decide) with h463 | h463
              · linarith only [h0, h2, h463, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h465 | h465
                · rcases m.htr 1 3 4 (by decide) (by decide) with h466 | h466
                  · linarith only [h0, h2, h342, h465, h466, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h469 | h469
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                        · linarith only [h0, h2, h342, h465, h470, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h0, h2, h465, h470, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h466, h468, h469, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h463, h465, h468, hlam, hphi, u5ehi7, u5elo3]
                · linarith only [h2, h341, h465, hc12, hc23, hlam, hphi]
            · linarith only [h2, h341, h462, hlam, hphi, u5ehi7, u5elo3]
        · linarith only [h341, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h478 | h478
      · linarith only [h0, h1, h478, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h480 | h480
        · rcases m.htr 0 3 4 (by decide) (by decide) with h481 | h481
          · rcases m.htr 0 3 5 (by decide) (by decide) with h482 | h482
            · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
              · linarith only [h478, h480, h483, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
                · linarith only [h0, h1, h483, h485, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                · linarith only [h0, h1, h480, h483, h485, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h480, h482, hlam, hphi, u5ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h489 | h489
            · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
              · linarith only [h0, h1, h481, h490, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                · linarith only [h0, h1, h481, h492, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h0, h1, h480, h481, h492, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h1, h480, h489, hlam, hphi, u5ehi7, u5elo3]
        · linarith only [h480, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h497 | h497
    · rcases m.htr 0 2 3 (by decide) (by decide) with h498 | h498
      · rcases m.htr 0 2 5 (by decide) (by decide) with h499 | h499
        · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
          · rcases m.htr 0 3 5 (by decide) (by decide) with h501 | h501
            · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
              · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
                    · linarith only [h0, h497, h505, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h504, h505, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                    · linarith only [h0, h497, h500, h504, h508, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h510 | h510
                      · linarith only [h0, h497, h500, h504, h510, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                        · linarith only [h502, h504, h512, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h514 | h514
                          · linarith only [h502, h508, h514, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                            · linarith only [h0, h497, h500, h510, h516, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h502, h504, h516, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h503, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h497, h500, h502, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · linarith only [h500, h501, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h522 | h522
            · rcases m.htr 1 2 3 (by decide) (by decide) with h523 | h523
              · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
                  · linarith only [h497, h500, h522, h525, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                    · linarith only [h0, h497, h527, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h500, h522, h523, h527, hc23, hc34, hlam, hphi]
                · linarith only [h0, h524, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h497, h522, h523, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · linarith only [h522, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
        · linarith only [h498, h499, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h497, h498, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h535 | h535
      · rcases m.htr 0 2 5 (by decide) (by decide) with h536 | h536
        · rcases m.htr 0 3 4 (by decide) (by decide) with h537 | h537
          · rcases m.htr 0 3 5 (by decide) (by decide) with h538 | h538
            · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
              · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
                · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h546 | h546
                            · linarith only [h535, h544, h546, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h3bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h497, hlam, p548_1]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h0, h535, h545, hc12, hlam, hphi, ht01, ht0b, ht5b, p548_1, u5ehi8]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                rcases p548_3 (m.d 0 3) (by simp) with h552 | h552
                                · rcases p548_3 (m.d 1 3) (by simp) with h553 | h553
                                  · rcases p548_3 (m.d 2 3) (by simp) with h554 | h554
                                    · linarith only [h535, h554, hlam]
                                    · linarith only [h544, h554, hlam]
                                  · linarith only [h541, h553, hlam]
                                · linarith only [h552, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                rcases p548_3 (m.d 0 3) (by simp) with h559 | h559
                                · rcases p548_3 (m.d 1 3) (by simp) with h560 | h560
                                  · rcases p548_3 (m.d 2 3) (by simp) with h561 | h561
                                    · linarith only [h535, h561, hlam]
                                    · linarith only [h545, h561, hlam]
                                  · linarith only [h542, h560, hlam]
                                · linarith only [h559, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h539, hc12, hlam, hphi, ht01, p548_1, u0ehi2]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h539, h545, hc12, hlam, hphi, ht01, ht0b, ht5b, p548_1, u5ehi8]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                rcases p548_3 (m.d 0 3) (by simp) with h569 | h569
                                · linarith only [h497, h569, hlam]
                                · linarith only [h537, h569, hlam]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                rcases p548_3 (m.d 0 3) (by simp) with h572 | h572
                                · linarith only [h497, h572, hlam]
                                · linarith only [h538, h572, hlam]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h535, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h539, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                rcases p548_3 (m.d 0 3) (by simp) with h578 | h578
                                · rcases p548_3 (m.d 1 3) (by simp) with h579 | h579
                                  · rcases p548_3 (m.d 2 3) (by simp) with h580 | h580
                                    · rcases p548_3 (m.d 3 4) (by simp) with h581 | h581
                                      · linarith only [h581, hlam, p548_0]
                                      · rcases p548_3 (m.d 3 5) (by simp) with h583 | h583
                                        · linarith only [h545, h583, hlam]
                                        · linarith only [h546, h583, hlam]
                                    · linarith only [h580, hlam, p548_0]
                                  · linarith only [h541, h579, hlam]
                                · linarith only [h537, h578, hlam]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h0, h535, hc12, hlam, hphi, ht01, ht0b, ht5b, p548_1, u5ehi8]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h537, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h541, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h544, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h546, hlam, p548_1]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h538, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h542, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h545, hlam, p548_0]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [h545, hc34, hlam, hphi, ht45, p548_1, u5elo2]
                              · have p548_0 := h548c.1
                                have p548_1 := h548c.2.1
                                have p548_2 := h548c.2.2.1
                                have p548_3 := h548c.2.2.2
                                linarith only [hlam, p548_0]
                          · linarith only [h538, h544, h545, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                          · linarith only [h0, h535, h537, h544, h601, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h603 | h603
                            · rcases h3bigk with h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c | h604c
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h497, hlam, p604_1]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                rcases p604_3 (m.d 0 3) (by simp) with h607 | h607
                                · rcases p604_3 (m.d 1 3) (by simp) with h608 | h608
                                  · rcases p604_3 (m.d 2 3) (by simp) with h609 | h609
                                    · linarith only [h535, h609, hlam]
                                    · rcases p604_3 (m.d 3 4) (by simp) with h611 | h611
                                      · linarith only [h537, h611, hlam]
                                      · linarith only [h544, h611, hlam]
                                  · linarith only [h539, h608, hlam]
                                · linarith only [h535, h607, hlam]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h0, h535, h603, hc12, hlam, hphi, ht01, ht0b, ht5b, p604_1, u5ehi9]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                rcases p604_3 (m.d 0 3) (by simp) with h617 | h617
                                · rcases p604_3 (m.d 1 3) (by simp) with h618 | h618
                                  · rcases p604_3 (m.d 2 3) (by simp) with h619 | h619
                                    · linarith only [h535, h619, hlam]
                                    · rcases p604_3 (m.d 3 4) (by simp) with h621 | h621
                                      · linarith only [h537, h621, hlam]
                                      · linarith only [h603, h621, hlam]
                                  · linarith only [h542, h618, hlam]
                                · linarith only [h617, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h539, hc12, hlam, hphi, ht01, p604_1, u0ehi2]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                rcases p604_3 (m.d 0 3) (by simp) with h628 | h628
                                · linarith only [h497, h628, hlam]
                                · linarith only [h535, h628, hlam]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h603, hc13, hlam, hphi, ht01, ht0b, ht5b, p604_1, u5ehi9]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                rcases p604_3 (m.d 0 3) (by simp) with h632 | h632
                                · linarith only [h497, h632, hlam]
                                · linarith only [h538, h632, hlam]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h535, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h539, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h544, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h601, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h537, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h541, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                rcases p604_3 (m.d 0 3) (by simp) with h642 | h642
                                · rcases p604_3 (m.d 1 3) (by simp) with h643 | h643
                                  · rcases p604_3 (m.d 2 3) (by simp) with h644 | h644
                                    · linarith only [h644, hlam, p604_0]
                                    · rcases p604_3 (m.d 3 4) (by simp) with h646 | h646
                                      · rcases p604_3 (m.d 3 5) (by simp) with h647 | h647
                                        · linarith only [h603, h647, hlam]
                                        · linarith only [h601, h647, hlam]
                                      · linarith only [h646, hlam, p604_0]
                                  · linarith only [h539, h643, hlam]
                                · linarith only [h535, h642, hlam]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h537, h601, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p604_1]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h538, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h542, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [hc23, hlam, hphi, ht34, ht45, p604_1, u5elo3]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [h603, hlam, p604_0]
                              · have p604_0 := h604c.1
                                have p604_1 := h604c.2.1
                                have p604_2 := h604c.2.2.1
                                have p604_3 := h604c.2.2.2
                                linarith only [hlam, p604_0]
                            · linarith only [h543, h544, h603, hc23, hlam, hphi, ht34, ht45, u5elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h661 | h661
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h662 | h662
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h663 | h663
                            · linarith only [h541, h543, h663, hlam]
                            · rcases h3bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h497, hlam, p665_1]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h497, h539, h662, hc12, hlam, hphi, ht01, ht0b, ht5b, p665_1, u5ehi8]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                rcases p665_3 (m.d 0 3) (by simp) with h669 | h669
                                · rcases p665_3 (m.d 1 3) (by simp) with h670 | h670
                                  · rcases p665_3 (m.d 2 3) (by simp) with h671 | h671
                                    · linarith only [h535, h671, hlam]
                                    · linarith only [h661, h671, hlam]
                                  · linarith only [h541, h670, hlam]
                                · linarith only [h669, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                rcases p665_3 (m.d 0 3) (by simp) with h676 | h676
                                · rcases p665_3 (m.d 1 3) (by simp) with h677 | h677
                                  · rcases p665_3 (m.d 2 3) (by simp) with h678 | h678
                                    · linarith only [h535, h678, hlam]
                                    · linarith only [h662, h678, hlam]
                                  · linarith only [h542, h677, hlam]
                                · linarith only [h676, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h539, hc12, hlam, hphi, ht01, p665_1, u0ehi2]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h539, h662, hc12, hlam, hphi, ht01, ht0b, ht5b, p665_1, u5ehi8]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                rcases p665_3 (m.d 0 3) (by simp) with h686 | h686
                                · linarith only [h497, h686, hlam]
                                · linarith only [h537, h686, hlam]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                rcases p665_3 (m.d 0 3) (by simp) with h689 | h689
                                · linarith only [h497, h689, hlam]
                                · linarith only [h538, h689, hlam]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h535, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h539, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                rcases p665_3 (m.d 0 3) (by simp) with h695 | h695
                                · rcases p665_3 (m.d 1 3) (by simp) with h696 | h696
                                  · rcases p665_3 (m.d 2 3) (by simp) with h697 | h697
                                    · rcases p665_3 (m.d 3 4) (by simp) with h698 | h698
                                      · linarith only [h698, hlam, p665_0]
                                      · rcases p665_3 (m.d 3 5) (by simp) with h700 | h700
                                        · linarith only [h662, h700, hlam]
                                        · linarith only [h663, h700, hlam]
                                    · linarith only [h697, hlam, p665_0]
                                  · linarith only [h541, h696, hlam]
                                · linarith only [h537, h695, hlam]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h0, h535, hc12, hlam, hphi, ht01, ht0b, ht5b, p665_1, u5ehi8]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h537, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h541, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h661, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h663, hlam, p665_1]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h538, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h542, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [h662, hlam, p665_0]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [hc34, hlam, hphi, ht45, p665_1, u5elo3]
                              · have p665_0 := h665c.1
                                have p665_1 := h665c.2.1
                                have p665_2 := h665c.2.2.1
                                have p665_3 := h665c.2.2.2
                                linarith only [hlam, p665_0]
                          · linarith only [h542, h543, h661, h662, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h541, h543, h661, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h497, h538, h542, hc03, hlam, hphi, u0ehi0]
                  · linarith only [h497, h541, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h0, h540, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
              · linarith only [h0, h539, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h537, h538, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h724 | h724
            · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
              · rcases m.htr 1 2 5 (by decide) (by decide) with h726 | h726
                · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
                  · linarith only [h497, h537, h725, h727, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h497, h727, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h0, h726, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]
              · linarith only [h0, h535, h725, hc02, hlam, hphi, u0ehi0]
            · linarith only [h497, h724, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo3]
        · linarith only [h536, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h734 | h734
        · rcases m.htr 0 3 4 (by decide) (by decide) with h735 | h735
          · rcases m.htr 0 3 5 (by decide) (by decide) with h736 | h736
            · rcases m.htr 1 2 3 (by decide) (by decide) with h737 | h737
              · linarith only [h0, h535, h737, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h737, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h535, h734, h736, hlam, hphi, u5ehi7, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h741 | h741
            · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
              · linarith only [h0, h535, h742, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h0, h742, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h535, h734, h741, hlam, hphi, u5ehi7, u5elo3]
        · linarith only [h0, h734, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo2]

end R2N4
