import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_I_L_0_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h10, h11, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h11, h13, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                          · linarith only [h11, h15, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · linarith only [h15, h4, h7, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                    · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h19, h20, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                        · linarith only [h20, h22, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h24, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                            · linarith only [h26, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                            · rcases h0bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h22, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h22, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h20, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h20, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h0, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h20, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h20, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h1, hlam, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h4, hlam, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h20, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h3, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p28_1, u2elo0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h2, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h5, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h7, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h9, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h3, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h6, hlam, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h8, hlam, p28_0]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [h20, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                              · have p28_0 := h28c.1
                                have p28_1 := h28c.2.1
                                have p28_2 := h28c.2.2.1
                                have p28_3 := h28c.2.2.2
                                linarith only [hlam, p28_0]
                    · linarith only [h19, h4, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
                  · linarith only [h55, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                      · linarith only [h57, h58, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                      · linarith only [h58, h7, h8, hc23, hc35, hlam, hphi]
                    · linarith only [h4, h57, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h62 | h62
                · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h64, h65, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                          · linarith only [h5, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · linarith only [h5, h63, h68, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                        · linarith only [h62, h67, h7, hc23, hc34, hlam, hphi]
                    · linarith only [h4, h64, hc12, hlam, hphi, u2elo0]
                  · linarith only [h62, h63, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                      · linarith only [h75, h76, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h0, h62, h75, h78, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                          · linarith only [h5, h80, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · linarith only [h5, h74, h80, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                    · linarith only [h4, h75, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                      · linarith only [h4, h7, h85, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h1, h62, h84, h87, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h5, h89, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                            · rcases h0bigk with h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                rcases p92_3 (m.d 0 1) (by simp) with h95 | h95
                                · rcases p92_3 (m.d 0 2) (by simp) with h96 | h96
                                  · linarith only [h0, h96, hlam]
                                  · linarith only [h4, h96, hlam]
                                · linarith only [h1, h95, hlam]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p92_1, u4ehi0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h2, h74, hc01, hlam, hphi, ht0b, ht45, ht5b, p92_1, u4ehi1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h0, hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h1, h2, h74, h91, hc13, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p92_1, u2elo0, u4ehi1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p92_1, u2elo0, u4ehi1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h2, h74, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p92_1, u2elo0, u4ehi1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h1, hlam, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h4, hlam, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h7, hlam, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h62, hlam, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h2, hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h5, hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h1, h74, h91, hc13, hc34, hlam, hphi, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h74, hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h3, hlam, p92_0]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h6, hlam, p92_1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h1, h2, h6, h74, h91, hc13, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p92_1, u2elo0, u4ehi1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [h2, h74, h91, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p92_1, u4ehi1]
                              · have p92_0 := h92c.1
                                have p92_1 := h92c.2.1
                                have p92_2 := h92c.2.2.1
                                have p92_3 := h92c.2.2.2
                                linarith only [hlam, p92_0]
                            · rcases h0bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p122_1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                rcases p122_3 (m.d 0 1) (by simp) with h125 | h125
                                · rcases p122_3 (m.d 0 2) (by simp) with h126 | h126
                                  · linarith only [h0, h126, hlam]
                                  · linarith only [h126, h4, hlam]
                                · linarith only [h1, h125, hlam]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p122_1, u4ehi0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h6, h89, hc01, hlam, hphi, ht0b, ht45, ht5b, p122_1, u4ehi2]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h0, hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p122_1, u2elo0, u4ehi1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p122_1, u2elo0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h1, hlam, p122_1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h4, hlam, p122_1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h7, hlam, p122_1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h62, hlam, p122_1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h2, hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h5, hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h74, hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h3, hlam, p122_0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h6, hlam, p122_1]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h1, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p122_1, u2elo0, u4ehi0]
                              · have p122_0 := h122c.1
                                have p122_1 := h122c.2.1
                                have p122_2 := h122c.2.2.1
                                have p122_3 := h122c.2.2.2
                                linarith only [hlam, p122_0]
                    · linarith only [h4, h84, hc12, hlam, hphi, u2elo0]
            · linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
            · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
              · linarith only [h155, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
                · rcases m.htr 0 4 5 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                      · linarith only [h155, h157, h160, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                        · linarith only [h0, h159, h162, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h157, h162, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h159, h4, h5, hc12, hlam, hphi, u2elo3]
                  · linarith only [h154, h158, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                      · linarith only [h168, h169, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h0, h157, h168, h171, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                          · linarith only [h154, h173, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                          · linarith only [h154, h167, h173, h5, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h168, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h154, h167, h5, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
              · linarith only [h178, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h180 | h180
                · linarith only [h154, h180, h4, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h182 | h182
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                      · linarith only [h178, h184, h4, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                        · linarith only [h0, h154, h180, h183, h186, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                            · rcases h0bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h0, h183, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                rcases p190_3 (m.d 0 1) (by simp) with h193 | h193
                                · rcases p190_3 (m.d 0 2) (by simp) with h194 | h194
                                  · linarith only [h0, h194, hlam]
                                  · linarith only [h194, h4, hlam]
                                · linarith only [h1, h193, hlam]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h182, hc01, hlam, hphi, ht0b, ht45, ht5b, p190_1, u4ehi4]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h0, h154, h183, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h0, hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h1, h154, h183, h188, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p190_1, u2elo3]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h5, hlam, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h154, hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h1, hlam, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h4, hlam, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h178, hlam, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h180, hlam, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h2, hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h0, h183, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h1, h183, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p190_1, u2elo3]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h0, h154, h183, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p190_1, u2elo3]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h3, hlam, p190_0]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h0, h183, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h1, h154, h183, h188, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p190_1, u2elo3]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [h182, hlam, p190_1]
                              · have p190_0 := h190c.1
                                have p190_1 := h190c.2.1
                                have p190_2 := h190c.2.2.1
                                have p190_3 := h190c.2.2.2
                                linarith only [hlam, p190_0]
                            · linarith only [h0, h183, h184, h189, h5, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h182, h188, h5, hlam]
                    · linarith only [h183, h4, h5, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                      · linarith only [h223, h224, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                        · linarith only [h226, h4, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
                          · linarith only [h0, h182, h223, h228, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · linarith only [h0, h223, h228, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h223, h4, h5, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h232 | h232
          · linarith only [h232, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h234 | h234
            · rcases m.htr 0 3 4 (by decide) (by decide) with h235 | h235
              · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
                · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                    · linarith only [h238, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h232, h234, h240, h242, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                          · linarith only [h232, h234, h235, h237, h242, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h236, h241, h4, hlam]
                      · linarith only [h235, h240, h4, hlam]
                  · linarith only [h232, h234, h237, hlam]
                · linarith only [h234, h236, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 0 4 5 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                    · linarith only [h0, h251, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h235, h249, h253, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h256 | h256
                          · linarith only [h234, h253, h256, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h234, h250, h253, h256, h4, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h234, h249, h250, h255, h4, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h234, h235, h250, h4, hlam]
                · linarith only [h234, h249, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
              · rcases m.htr 0 3 5 (by decide) (by decide) with h263 | h263
                · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                    · linarith only [h265, h4, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h269 | h269
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                            · linarith only [h262, h270, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                            · linarith only [h232, h264, h267, h270, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                          · linarith only [h232, h264, h269, hlam]
                        · linarith only [h232, h234, h263, h264, h267, h268, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi4]
                      · linarith only [h262, h267, h4, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h276 | h276
                    · linarith only [h0, h262, h276, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                          · linarith only [h264, h278, h280, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                            · linarith only [h232, h262, h280, h282, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h0bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                rcases p284_3 (m.d 0 1) (by simp) with h286 | h286
                                · rcases p284_3 (m.d 0 2) (by simp) with h287 | h287
                                  · linarith only [h0, h287, hlam]
                                  · rcases p284_3 (m.d 0 3) (by simp) with h289 | h289
                                    · linarith only [h1, h289, hlam]
                                    · linarith only [h289, h4, hlam]
                                · linarith only [h0, h286, hlam]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h263, h282, hc01, hlam, hphi, ht0b, ht45, ht5b, p284_1, u4ehi3]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p284_1, u4ehi1]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h263, h282, hc01, hlam, hphi, ht0b, ht45, ht5b, p284_1, u4ehi3]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h0, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h4, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h232, hlam, p284_1]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h234, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h1, hlam, p284_1]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h0, h4, hc12, hlam, hphi, p284_1, u2elo2]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h2, h4, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p284_1, u2elo2, u4ehi1]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h0, h234, h4, hc12, hlam, hphi, p284_1, u2elo2]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h2, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h0, h232, hc12, hlam, hphi, p284_1, u2elo3]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h262, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h264, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h3, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h0, h234, h279, hc12, hlam, hphi, p284_1, u2elo2]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h263, hlam, p284_0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [h234, h279, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p284_1, u2elo2, u4ehi0]
                              · have p284_0 := h284c.1
                                have p284_1 := h284c.2.1
                                have p284_2 := h284c.2.2.1
                                have p284_3 := h284c.2.2.2
                                linarith only [hlam, p284_0]
                        · linarith only [h263, h279, h4, hlam]
                      · linarith only [h0, h232, h262, h278, h4, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h318 | h318
                  · linarith only [h262, h263, h318, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
                    · linarith only [h0, h320, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                        · linarith only [h262, h263, h323, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                          · linarith only [h262, h263, h318, h322, h323, h325, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
                            · linarith only [h232, h262, h325, h327, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h262, h323, h327, h4, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h262, h322, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h331 | h331
                · rcases m.htr 0 4 5 (by decide) (by decide) with h332 | h332
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h333 | h333
                    · linarith only [h0, h333, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                      · linarith only [h262, h331, h335, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h339 | h339
                            · rcases h0bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                rcases p340_3 (m.d 0 1) (by simp) with h342 | h342
                                · rcases p340_3 (m.d 0 2) (by simp) with h343 | h343
                                  · linarith only [h0, h343, hlam]
                                  · rcases p340_3 (m.d 0 3) (by simp) with h345 | h345
                                    · linarith only [h1, h345, hlam]
                                    · linarith only [h345, h4, hlam]
                                · linarith only [h0, h342, hlam]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h331, h339, hc01, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi4]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h262, h331, h339, hc01, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi4]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h331, h339, hc01, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi4]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h0, hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h4, hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h232, hlam, p340_1]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h234, hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h1, hlam, p340_1]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h0, h335, h4, hc12, hc34, hlam, hphi, ht23, p340_1]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h262, hlam, p340_1]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h331, h335, h339, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p340_1, u4ehi4]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h2, hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h0, h232, hc12, hlam, hphi, p340_1, u2elo3]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h232, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p340_1, u2elo3]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h232, h331, h339, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p340_1, u2elo3, u4ehi4]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h3, hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h0, h234, h335, h337, hc12, hc34, hlam, hphi, ht23, p340_1]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h331, hlam, p340_0]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [h332, hlam, p340_1]
                              · have p340_0 := h340c.1
                                have p340_1 := h340c.2.1
                                have p340_2 := h340c.2.2.1
                                have p340_3 := h340c.2.2.2
                                linarith only [hlam, p340_0]
                            · linarith only [h0, h335, h339, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h232, h332, h338, hlam]
                        · linarith only [h331, h337, h4, hlam]
                  · linarith only [h262, h331, h332, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
                    · linarith only [h0, h377, h4, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                      · linarith only [h1, h262, h377, h379, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                        · linarith only [h1, h331, h377, h379, h381, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
                            · rcases h0bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 1) (by simp) with h387 | h387
                                · rcases p385_3 (m.d 0 2) (by simp) with h388 | h388
                                  · linarith only [h0, h388, hlam]
                                  · rcases p385_3 (m.d 0 3) (by simp) with h390 | h390
                                    · linarith only [h1, h390, hlam]
                                    · linarith only [h390, h4, hlam]
                                · linarith only [h0, h387, hlam]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                rcases p385_3 (m.d 0 1) (by simp) with h394 | h394
                                · rcases p385_3 (m.d 0 2) (by simp) with h395 | h395
                                  · linarith only [h0, h395, hlam]
                                  · rcases p385_3 (m.d 0 3) (by simp) with h397 | h397
                                    · linarith only [h1, h397, hlam]
                                    · rcases p385_3 (m.d 0 4) (by simp) with h399 | h399
                                      · linarith only [h2, h399, hlam]
                                      · linarith only [h262, h399, hlam]
                                · linarith only [h1, h394, hlam]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p385_1, u4ehi0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h376, hc01, hlam, hphi, ht0b, ht45, ht5b, p385_1, u4ehi4]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h0, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h4, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h232, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h234, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h1, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h0, h381, h383, h4, hc12, hlam, hphi, p385_1, u2elo3]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h262, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h331, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h2, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h0, h232, hc12, hlam, hphi, p385_1, u2elo3]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h232, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p385_1, u2elo3]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h232, h376, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p385_1, u2elo3, u4ehi4]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h3, hlam, p385_0]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h0, h234, h383, hc12, hlam, hphi, p385_1, u2elo3]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h1, h234, h377, h383, hc12, hlam, hphi, p385_1, u2elo3]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [h376, hlam, p385_1]
                              · have p385_0 := h385c.1
                                have p385_1 := h385c.2.1
                                have p385_2 := h385c.2.2.1
                                have p385_3 := h385c.2.2.2
                                linarith only [hlam, p385_0]
                            · linarith only [h262, h376, h384, hlam]
                          · linarith only [h232, h376, h383, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
                    · linarith only [h0, h4, h427, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                      · linarith only [h0, h262, h4, h429, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h431 | h431
                        · linarith only [h0, h331, h4, h429, h431, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
                          · linarith only [h376, h433, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                            · linarith only [h0, h4, h429, h433, h435, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h4, h429, h435, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h438 | h438
        · rcases m.htr 0 2 4 (by decide) (by decide) with h439 | h439
          · rcases m.htr 0 2 5 (by decide) (by decide) with h440 | h440
            · linarith only [h0, h3, h440, hlam]
            · linarith only [h439, h440, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
            · linarith only [h2, h3, h439, h443, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h445 | h445
              · linarith only [h438, h439, h445, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h447 | h447
                · linarith only [h2, h3, h438, h439, h447, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
                  · linarith only [h2, h3, h449, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h452 | h452
                      · linarith only [h1, h3, h445, h451, h452, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
                        · linarith only [h0, h3, h447, h454, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                          · linarith only [h449, h456, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · linarith only [h0, h439, h451, h456, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h438, h439, h451, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h460 | h460
          · linarith only [h438, h460, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h462 | h462
            · linarith only [h0, h3, h438, h462, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h464 | h464
              · rcases m.htr 0 3 5 (by decide) (by decide) with h465 | h465
                · linarith only [h1, h3, h465, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                  · linarith only [h1, h3, h464, h467, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
                    · linarith only [h438, h469, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h464, h465, h472, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                          · linarith only [h1, h3, h464, h467, h474, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                            · linarith only [h1, h464, h474, h476, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h438, h464, h472, h476, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h438, h464, h471, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h480 | h480
                · linarith only [h2, h3, h464, h480, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h482 | h482
                  · linarith only [h2, h3, h482, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                    · linarith only [h0, h3, h438, h462, h484, hc02, hlam, hphi, u2elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                      · linarith only [h0, h438, h464, h486, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                        · linarith only [h2, h3, h480, h486, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h490 | h490
                          · linarith only [h2, h482, h490, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h492 | h492
                            · linarith only [h0, h438, h486, h490, h492, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h438, h486, h492, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h495 | h495
      · rcases m.htr 0 2 3 (by decide) (by decide) with h496 | h496
        · rcases m.htr 0 2 4 (by decide) (by decide) with h497 | h497
          · linarith only [h0, h2, h497, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h499 | h499
            · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
              · linarith only [h496, h497, h500, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
                · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                      · linarith only [h0, h500, h504, h505, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                        · linarith only [h0, h2, h497, h504, h507, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h496, h497, h502, h507, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h496, h497, h504, hc12, hlam, hphi, u2elo3]
                  · linarith only [h2, h495, h503, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                      · linarith only [h0, h513, h514, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                        · linarith only [h0, h2, h497, h502, h513, h516, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h518 | h518
                          · linarith only [h497, h499, h518, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                          · linarith only [h0, h2, h497, h513, h518, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h496, h497, h513, hc12, hlam, hphi, u2elo3]
                  · linarith only [h0, h2, h497, h499, h512, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
              · linarith only [h496, h499, h523, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h525 | h525
                · linarith only [h496, h499, h525, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                      · linarith only [h523, h528, h529, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                        · linarith only [h1, h2, h497, h499, h525, h528, h531, hc02, hlam, hphi, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                            · rcases h0bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h0, h2, h497, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h2, h497, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h2, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h0, h2, h497, h499, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h0, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h1, h499, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p535_1, u2elo4]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h497, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h499, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h1, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h496, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h523, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h525, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h497, hc01, hlam, hphi, ht12, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h497, hc02, hlam, hphi, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h1, h497, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h0, h497, h499, h528, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p535_1, u2elo3]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h495, hlam, p535_0]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h0, h528, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h1, h2, h495, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [h527, hlam, p535_1]
                              · have p535_0 := h535c.1
                                have p535_1 := h535c.2.1
                                have p535_2 := h535c.2.2.1
                                have p535_3 := h535c.2.2.2
                                linarith only [hlam, p535_0]
                            · linarith only [h0, h2, h497, h528, h529, h534, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h497, h527, h533, hlam]
                    · linarith only [h496, h499, h528, hc12, hlam, hphi, u2elo4]
                  · linarith only [h2, h495, h527, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h565 | h565
          · linarith only [h496, h565, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h567 | h567
            · rcases m.htr 0 3 4 (by decide) (by decide) with h568 | h568
              · linarith only [h1, h2, h568, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h570 | h570
                · rcases m.htr 0 4 5 (by decide) (by decide) with h571 | h571
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                    · linarith only [h496, h572, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h574 | h574
                      · linarith only [h1, h568, h572, h574, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h577 | h577
                          · linarith only [h496, h567, h574, h577, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                          · linarith only [h2, h495, h565, h571, h577, hlam]
                        · linarith only [h496, h567, h570, h571, h576, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h2, h496, h567, h571, hc12, hlam, hphi, u2elo2]
                · linarith only [h496, h567, h570, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h583 | h583
              · linarith only [h1, h2, h583, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 4 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h587 | h587
                    · linarith only [h496, h587, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                      · linarith only [h583, h585, h589, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h592 | h592
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h593 | h593
                            · rcases h0bigk with h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h0, h2, h565, hc12, hlam, hphi, p594_1, u2elo3]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h2, h565, h585, h593, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p594_1, u2elo3, u4ehi4]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h2, hlam, p594_1]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h2, h565, h585, h593, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p594_1, u2elo3, u4ehi4]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h0, hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h496, hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h565, hlam, p594_1]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h567, hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h1, hlam, p594_1]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h0, h1, h2, h565, hc12, hlam, hphi, p594_1, u2elo3]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h583, hlam, p594_1]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h1, h2, h565, h585, h593, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p594_1, u2elo3, u4ehi4]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h565, hc01, hlam, hphi, ht12, p594_1, u2elo3]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h0, h565, hc12, hlam, hphi, p594_1, u2elo3]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h565, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p594_1, u2elo3]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h565, h585, h593, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p594_1, u2elo3, u4ehi4]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h495, hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h0, h2, h495, h496, h585, h589, h593, hc12, hc14, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p594_1, u4ehi4]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h585, hlam, p594_0]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [h586, hlam, p594_1]
                              · have p594_0 := h594c.1
                                have p594_1 := h594c.2.1
                                have p594_2 := h594c.2.2.1
                                have p594_3 := h594c.2.2.2
                                linarith only [hlam, p594_0]
                            · linarith only [h0, h496, h589, h593, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h565, h586, h592, hlam]
                        · linarith only [h0, h1, h2, h496, h565, h585, h591, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h2, h585, h586, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h625 | h625
                    · linarith only [h0, h2, h496, h625, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                      · linarith only [h0, h496, h583, h627, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                        · linarith only [h0, h496, h585, h627, h629, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h631 | h631
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h632 | h632
                            · rcases h0bigk with h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, h2, h565, hc12, hlam, hphi, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, h2, h496, h565, hc12, hlam, hphi, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h2, hlam, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h2, h565, h624, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p633_1, u2elo3, u4ehi4]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h496, hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h565, hlam, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h567, hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h1, hlam, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, h1, h2, h565, hc12, hlam, hphi, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h583, hlam, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h585, hlam, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h565, hc01, hlam, hphi, ht12, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, h565, hc12, hlam, hphi, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h565, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h565, h624, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p633_1, u2elo3, u4ehi4]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h495, hlam, p633_0]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, h2, h495, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h0, h2, h495, h496, h565, hc12, hlam, hphi, p633_1, u2elo3]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [h624, hlam, p633_1]
                              · have p633_0 := h633c.1
                                have p633_1 := h633c.2.1
                                have p633_2 := h633c.2.2.1
                                have p633_3 := h633c.2.2.2
                                linarith only [hlam, p633_0]
                            · linarith only [h583, h624, h632, hlam]
                          · linarith only [h565, h624, h631, hlam]
                  · linarith only [h2, h495, h624, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h662 | h662
        · rcases m.htr 0 2 4 (by decide) (by decide) with h663 | h663
          · linarith only [h0, h2, h663, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h665 | h665
            · linarith only [h0, h495, h663, h665, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h667 | h667
              · linarith only [h662, h663, h667, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h669 | h669
                · linarith only [h0, h495, h662, h663, h669, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                      · linarith only [h0, h667, h672, h673, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                        · linarith only [h0, h495, h669, h675, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h677 | h677
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h678 | h678
                            · rcases h0bigk with h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, h672, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h2, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h495, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p679_1, u2elo0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h663, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h665, hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h1, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h662, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h667, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h669, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h663, hc01, hlam, hphi, ht12, p679_1, u2elo3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h663, hc02, hlam, hphi, p679_1, u2elo3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h1, h663, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p679_1, u2elo3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h495, h663, hc01, hlam, hphi, ht12, p679_1, u2elo3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, h672, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h0, h665, h672, h677, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p679_1, u2elo3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h1, h665, h677, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p679_1, u2elo3]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [h671, hlam, p679_1]
                              · have p679_0 := h679c.1
                                have p679_1 := h679c.2.1
                                have p679_2 := h679c.2.2.1
                                have p679_3 := h679c.2.2.2
                                linarith only [hlam, p679_0]
                            · linarith only [h663, h671, h673, h678, hlam]
                          · linarith only [h663, h671, h677, hlam]
                    · linarith only [h662, h672, hc12, hlam, hphi, u2elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h708 | h708
                    · linarith only [h0, h2, h671, h708, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h662, h663, h708, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h711 | h711
          · linarith only [h662, h711, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h713 | h713
            · linarith only [h0, h495, h662, h713, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h715 | h715
              · linarith only [h1, h2, h715, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h717 | h717
                · linarith only [h1, h495, h717, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h719 | h719
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
                    · linarith only [h662, h720, hc02, hlam, hphi, u2elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h722 | h722
                      · linarith only [h0, h662, h715, h722, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h724 | h724
                        · linarith only [h0, h495, h717, h722, h724, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h726 | h726
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h727 | h727
                            · rcases h0bigk with h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c | h728c
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h2, h662, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h2, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h495, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h662, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h711, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h713, hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h715, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h717, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h711, hc01, hlam, hphi, ht12, p728_1, u2elo3]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h711, hc12, hlam, hphi, p728_1, u2elo3]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h711, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p728_1, u2elo3]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, h495, h711, h720, hc12, hlam, hphi, p728_1, u2elo3]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, h720, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h0, h713, h726, hc12, hlam, hphi, p728_1, u2elo3]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h1, h713, h720, h726, hc12, hlam, hphi, p728_1, u2elo3]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [h719, hlam, p728_1]
                              · have p728_0 := h728c.1
                                have p728_1 := h728c.2.1
                                have p728_2 := h728c.2.2.1
                                have p728_3 := h728c.2.2.2
                                linarith only [hlam, p728_0]
                            · linarith only [h711, h719, h727, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                          · linarith only [h711, h719, h726, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h756 | h756
                    · linarith only [h0, h662, h756, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h758 | h758
                      · linarith only [h0, h662, h715, h758, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h760 | h760
                        · linarith only [h717, h758, h760, hc03, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h762 | h762
                          · linarith only [h719, h762, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h764 | h764
                            · linarith only [h0, h662, h758, h762, h764, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h662, h758, h764, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h767 | h767
    · rcases m.htr 0 1 5 (by decide) (by decide) with h768 | h768
      · rcases m.htr 0 2 3 (by decide) (by decide) with h769 | h769
        · linarith only [h0, h1, h769, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h771 | h771
          · linarith only [h769, h771, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h773 | h773
            · rcases m.htr 0 3 4 (by decide) (by decide) with h774 | h774
              · rcases m.htr 0 3 5 (by decide) (by decide) with h775 | h775
                · rcases m.htr 0 4 5 (by decide) (by decide) with h776 | h776
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h777 | h777
                    · linarith only [h769, h777, hc02, hlam, hphi, u2elo1]
                    · linarith only [h1, h767, h776, h777, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h771, h773, h776, hlam]
                · linarith only [h0, h1, h771, h773, h775, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h767, h774, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h783 | h783
              · rcases m.htr 0 3 5 (by decide) (by decide) with h784 | h784
                · rcases m.htr 0 4 5 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h786 | h786
                    · linarith only [h1, h767, h769, h785, h786, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                    · linarith only [h1, h767, h785, h786, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h789 | h789
                    · linarith only [h0, h1, h769, h789, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h789, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h768, h784, hlam]
              · linarith only [h1, h767, h783, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h794 | h794
        · linarith only [h0, h1, h794, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h796 | h796
          · linarith only [h794, h796, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h798 | h798
            · linarith only [h0, h768, h794, h798, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h800 | h800
              · rcases m.htr 0 3 5 (by decide) (by decide) with h801 | h801
                · rcases m.htr 0 4 5 (by decide) (by decide) with h802 | h802
                  · linarith only [h767, h768, h802, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
                    · linarith only [h794, h804, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1, h804, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h807 | h807
                  · linarith only [h1, h767, h801, h807, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h809 | h809
                    · linarith only [h0, h1, h801, h809, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1, h809, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h767, h800, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h813 | h813
      · rcases m.htr 0 2 3 (by decide) (by decide) with h814 | h814
        · linarith only [h0, h1, h814, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h816 | h816
          · linarith only [h814, h816, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h818 | h818
            · rcases m.htr 0 3 4 (by decide) (by decide) with h819 | h819
              · rcases m.htr 0 3 5 (by decide) (by decide) with h820 | h820
                · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
                    · linarith only [h814, h818, h822, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1, h822, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h767, h818, h821, hlam]
                · linarith only [h816, h818, h819, h820, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h827 | h827
                · rcases m.htr 0 4 5 (by decide) (by decide) with h828 | h828
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h829 | h829
                    · linarith only [h0, h1, h814, h829, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h829, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h1, h816, h818, h819, h828, hc12, hlam, hphi, u2elo3]
                · linarith only [h0, h1, h816, h818, h827, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h834 | h834
              · rcases m.htr 0 3 5 (by decide) (by decide) with h835 | h835
                · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                    · linarith only [h0, h814, h834, h836, h837, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1, h837, hc12, hlam, hphi, u2elo2]
                  · linarith only [h767, h813, h836, hlam]
                · linarith only [h1, h813, h835, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h842 | h842
                · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h844 | h844
                    · linarith only [h0, h1, h834, h844, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h844, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1, h813, h834, h843, hlam]
                · linarith only [h1, h813, h842, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h849 | h849
        · linarith only [h0, h1, h849, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h851 | h851
          · linarith only [h849, h851, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h853 | h853
            · linarith only [h0, h813, h849, h853, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h855 | h855
              · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
                · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h858 | h858
                    · linarith only [h0, h1, h849, h858, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h858, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h861 | h861
                    · linarith only [h0, h1, h849, h856, h857, h861, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h1, h861, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h864 | h864
                  · linarith only [h855, h856, h864, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
                    · linarith only [h0, h767, h864, h866, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1, h866, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h869 | h869
                · rcases m.htr 0 4 5 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
                    · linarith only [h0, h1, h855, h871, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h871, hc12, hlam, hphi, u2elo2]
                  · linarith only [h855, h869, h870, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h875 | h875
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h876 | h876
                    · linarith only [h0, h1, h855, h876, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h876, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
                    · linarith only [h0, h1, h855, h879, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h879, hc12, hlam, hphi, u2elo2]

end R2N4
