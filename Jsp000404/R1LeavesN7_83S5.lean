import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_L_R_L_0_L_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h0, h10, h11, h5, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h5, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases h4bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h2, hlam, hphi, ht12, p16_1, u1ehi3, u2elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h19 | h19
                            · rcases p16_3 (m.d 1 4) (by simp) with h20 | h20
                              · linarith only [h1, h20, hlam]
                              · linarith only [h20, h6, hlam]
                            · linarith only [h19, h2, hlam]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h24 | h24
                            · rcases p16_3 (m.d 1 4) (by simp) with h25 | h25
                              · linarith only [h1, h25, hlam]
                              · linarith only [h25, h7, hlam]
                            · linarith only [h24, h3, hlam]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h2, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h32 | h32
                            · rcases p16_3 (m.d 1 4) (by simp) with h33 | h33
                              · rcases p16_3 (m.d 2 4) (by simp) with h34 | h34
                                · linarith only [h34, h6, hlam]
                                · rcases p16_3 (m.d 3 4) (by simp) with h36 | h36
                                  · linarith only [h36, h7, hlam]
                                  · rcases p16_3 (m.d 4 5) (by simp) with h38 | h38
                                    · linarith only [h38, h8, hlam]
                                    · linarith only [h10, h38, hlam]
                              · linarith only [h33, h6, hlam]
                            · linarith only [h2, h32, hlam]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            rcases p16_3 (m.d 0 4) (by simp) with h43 | h43
                            · rcases p16_3 (m.d 1 4) (by simp) with h44 | h44
                              · rcases p16_3 (m.d 2 4) (by simp) with h45 | h45
                                · linarith only [h45, h6, hlam]
                                · linarith only [h45, h9, hlam]
                              · linarith only [h44, h7, hlam]
                            · linarith only [h3, h43, hlam]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, h10, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h2, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h6, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, hc34, hc45, hlam, hphi, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h7, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h9, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h14, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h4, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h2, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h5, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                        · rcases h4bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hlam, hphi, ht12, p68_1, u1ehi3, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, h66, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p68_1, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 4) (by simp) with h73 | h73
                            · rcases p68_3 (m.d 1 4) (by simp) with h74 | h74
                              · linarith only [h1, h74, hlam]
                              · linarith only [h74, h8, hlam]
                            · linarith only [h73, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, h66, hc01, hc45, hlam, hphi, ht0b, ht5b, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h5, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 4) (by simp) with h82 | h82
                            · rcases p68_3 (m.d 1 4) (by simp) with h83 | h83
                              · rcases p68_3 (m.d 2 4) (by simp) with h84 | h84
                                · linarith only [h6, h84, hlam]
                                · linarith only [h66, h84, hlam]
                              · linarith only [h83, hlam, p68_0]
                            · linarith only [h4, h82, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h6, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h9, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p68_1, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h3, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h7, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h5, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p68_1, u2elo0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h4, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h8, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h66, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h67, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                        · linarith only [h2, h66, h67, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                        · linarith only [h0, h105, h5, h66, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h105, h2, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h2, h4, h8, hlam, hphi, ht12, u1ehi3, u2elo0]
                · linarith only [h2, h3, h7, hlam, hphi, ht12, u1ehi2, u2elo0]
              · linarith only [h6, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h5, hlam, hphi, ht12, u1ehi1, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
            · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
              · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                  · linarith only [h1, h115, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h118 | h118
                      · linarith only [h1, h117, h118, h4, hlam, hphi, ht12, u1ehi3, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h120 | h120
                        · linarith only [h0, h1, h112, h117, h120, h4, hlam, hphi, ht12, u1ehi3, u2elo0]
                        · rcases h4bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, p122_1, u1ehi3]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h4, hc24, hc45, hlam, hphi, p122_1]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h4, hc34, hc45, hlam, hphi, p122_1]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h4, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h1, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h1, h4, hc24, hc45, hlam, hphi, p122_1]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h1, h4, hc34, hc45, hlam, hphi, p122_1]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h115, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h2, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h113, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p122_1, u2elo0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h118, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h3, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h114, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h117, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h120, hlam, p122_0]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht12, ht23, ht34, p122_1, u1ehi3]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p122_1, u1ehi3]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            rcases p122_3 (m.d 0 4) (by simp) with h145 | h145
                            · linarith only [h145, h4, hlam]
                            · linarith only [h145, h2, hlam]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            rcases p122_3 (m.d 0 4) (by simp) with h148 | h148
                            · linarith only [h148, h4, hlam]
                            · linarith only [h148, h3, hlam]
                          · have p122_0 := h122c.1
                            have p122_1 := h122c.2.1
                            have p122_2 := h122c.2.2.1
                            have p122_3 := h122c.2.2.2
                            linarith only [hlam, p122_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h152 | h152
                      · linarith only [h0, h1, h112, h114, h117, h152, h4, hlam, hphi, ht12, u1ehi3, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h154 | h154
                        · linarith only [h0, h1, h112, h114, h154, h4, hlam, hphi, ht12, u1ehi3, u2elo0]
                        · rcases h4bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h0, h112, h114, h117, h4, hc23, hc45, hlam, hphi, ht12, ht34, p156_1, u1ehi3, u2elo0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h4, hc24, hc45, hlam, hphi, p156_1]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h117, h4, hc23, hc45, hlam, hphi, ht34, p156_1]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h4, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h1, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h1, h4, hc24, hc45, hlam, hphi, p156_1]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h1, h117, h4, hc23, hc45, hlam, hphi, ht34, p156_1]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h115, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h2, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h113, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h117, hlam, p156_1]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h152, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h3, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h114, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h0, h112, h114, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p156_1, u2elo0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h154, hlam, p156_0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h0, h1, h112, h114, h117, hc23, hc45, hlam, hphi, ht12, ht34, p156_1, u1ehi3, u2elo0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h0, h112, h114, h117, hc23, hc45, hlam, hphi, ht12, ht34, p156_1, u1ehi3, u2elo0]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            rcases p156_3 (m.d 0 4) (by simp) with h179 | h179
                            · linarith only [h179, h4, hlam]
                            · linarith only [h179, h2, hlam]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [h117, hc23, hc45, hlam, hphi, ht34, p156_1]
                          · have p156_0 := h156c.1
                            have p156_1 := h156c.2.1
                            have p156_2 := h156c.2.2.1
                            have p156_3 := h156c.2.2.2
                            linarith only [hlam, p156_0]
                · linarith only [h114, h2, h3, hlam, hphi, ht12, u1ehi2, u2elo0]
              · linarith only [h113, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h112, hlam, hphi, ht12, u1ehi1, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h187 | h187
          · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
            · rcases m.htr 1 2 4 (by decide) (by decide) with h189 | h189
              · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                · linarith only [h0, h1, h188, h190, h3, hlam, hphi, ht12, u1ehi3, u2elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                    · linarith only [h0, h188, h190, h193, hlam, hphi, ht12, u1ehi2, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                        · rcases h4bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h190, h2, hlam, hphi, ht12, p197_1, u1ehi2, u2elo0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h195, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1, u2elo0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h3, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 4) (by simp) with h202 | h202
                            · rcases p197_3 (m.d 1 4) (by simp) with h203 | h203
                              · linarith only [h1, h203, hlam]
                              · linarith only [h192, h203, hlam]
                            · linarith only [h202, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h1, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h1, h195, hc01, hc45, hlam, hphi, ht0b, ht5b, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h190, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 4) (by simp) with h211 | h211
                            · rcases p197_3 (m.d 1 4) (by simp) with h212 | h212
                              · rcases p197_3 (m.d 2 4) (by simp) with h213 | h213
                                · linarith only [h189, h213, hlam]
                                · linarith only [h195, h213, hlam]
                              · linarith only [h212, hlam, p197_0]
                            · linarith only [h187, h211, hlam]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h2, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h189, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h193, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1, u2elo0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, ht12, ht23, p197_1, u1ehi3]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h192, hc34, hlam, hphi, ht12, ht23, p197_1, u1ehi4]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 4) (by simp) with h225 | h225
                            · linarith only [h225, h3, hlam]
                            · linarith only [h2, h225, hlam]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 4) (by simp) with h229 | h229
                            · linarith only [h229, h3, hlam]
                            · linarith only [h187, h229, hlam]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h187, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h192, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h195, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h196, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                        · linarith only [h187, h196, h3, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                        · rcases h4bigk with h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h192, h193, h195, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p239_1]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            rcases p239_3 (m.d 0 4) (by simp) with h242 | h242
                            · rcases p239_3 (m.d 1 4) (by simp) with h243 | h243
                              · linarith only [h1, h243, hlam]
                              · linarith only [h189, h243, hlam]
                            · linarith only [h2, h242, hlam]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h3, hlam, p239_1]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h193, h195, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p239_1, u2elo0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h1, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            rcases p239_3 (m.d 0 4) (by simp) with h251 | h251
                            · rcases p239_3 (m.d 1 4) (by simp) with h252 | h252
                              · rcases p239_3 (m.d 2 4) (by simp) with h253 | h253
                                · linarith only [h189, h253, hlam]
                                · rcases p239_3 (m.d 3 4) (by simp) with h255 | h255
                                  · rcases p239_3 (m.d 4 5) (by simp) with h256 | h256
                                    · linarith only [h192, h256, hlam]
                                    · linarith only [h195, h256, hlam]
                                  · linarith only [h193, h255, hlam]
                              · linarith only [h189, h252, hlam]
                            · linarith only [h2, h251, hlam]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h190, hlam, p239_1]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h1, h193, h195, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p239_1]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h2, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h189, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h193, hlam, p239_1]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h195, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, ht12, ht23, p239_1, u1ehi3]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h187, h193, h195, h2, hc23, hc34, hlam, hphi, ht12, p239_1, u1ehi3, u2elo0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            rcases p239_3 (m.d 0 4) (by simp) with h271 | h271
                            · linarith only [h271, h3, hlam]
                            · linarith only [h2, h271, hlam]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h193, h195, hc23, hc34, hlam, hphi, p239_1]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h187, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h192, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h1, h192, h193, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p239_1, u2elo0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [h238, hlam, p239_0]
                          · have p239_0 := h239c.1
                            have p239_1 := h239c.2.1
                            have p239_2 := h239c.2.2.1
                            have p239_3 := h239c.2.2.2
                            linarith only [hlam, p239_0]
                        · linarith only [h1, h192, h2, h238, h3, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h187, h192, h2, hlam, hphi, ht12, u1ehi3, u2elo0]
              · linarith only [h189, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h188, hlam, hphi, ht12, u1ehi1, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
            · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
              · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                · linarith only [h1, h285, h287, h3, hlam, hphi, ht12, u1ehi3, u2elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                  · linarith only [h1, h187, h289, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                    · linarith only [h0, h285, h287, h291, hlam, hphi, ht12, u1ehi2, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h0, h1, h187, h286, h287, h293, hlam, hphi, ht12, u1ehi2, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                        · linarith only [h1, h187, h287, h295, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · linarith only [h287, h295, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h286, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h285, hlam, hphi, ht12, u1ehi1, u2elo2]
      · linarith only [h0, h2, hlam, hphi, ht12, u1ehi1, u2elo3]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem r1l7_11_13_25_L_0_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h3, h5, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                · linarith only [h0, h3, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h0, h3, h5, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h12, h3, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h0, h14, h3, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
            · rcases m.htr 0 3 5 (by decide) (by decide) with h18 | h18
              · linarith only [h1, h18, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, h3, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h22, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                    · linarith only [h1, h24, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · linarith only [h1, h17, h20, h24, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
              · linarith only [h17, h2, h27, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                · linarith only [h0, h29, h3, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h1, h29, h3, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h1, h17, h3, h33, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h27, h35, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h2, h3, h37, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h2, h29, h3, h33, h35, h40, hc12, hc23, hlam, hphi]
                            · linarith only [h17, h39, h40, hc03, hc35, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                            · linarith only [h2, h29, h3, h33, h39, h43, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht5b, u1elo4, u5ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                              · linarith only [h2, h29, h3, h33, h37, h45, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h39, h45, h5, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
        · linarith only [h2, h48, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h50 | h50
          · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
            · linarith only [h1, h2, h51, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h53 | h53
              · linarith only [h0, h2, h50, h53, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h2, h55, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h50, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
            · linarith only [h1, h2, h58, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
              · linarith only [h1, h2, h60, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
                · linarith only [h0, h2, h50, h62, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                  · linarith only [h64, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h66 | h66
                    · linarith only [h1, h2, h58, h66, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                      · linarith only [h1, h2, h60, h68, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                        · linarith only [h70, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · linarith only [h1, h2, h62, h70, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
      · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
        · linarith only [h1, h74, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h76 | h76
          · linarith only [h0, h1, h76, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h78 | h78
            · rcases m.htr 0 3 5 (by decide) (by decide) with h79 | h79
              · linarith only [h1, h79, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                · linarith only [h0, h1, h76, h81, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                  · linarith only [h0, h1, h83, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                      · linarith only [h86, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · linarith only [h0, h1, h86, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h85, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h73, h78, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h91 | h91
        · linarith only [h1, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h93 | h93
          · linarith only [h0, h1, h93, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
            · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
              · linarith only [h1, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                · linarith only [h0, h1, h93, h98, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                  · linarith only [h0, h1, h100, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h0, h103, h73, h95, h96, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h103, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h102, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
              · linarith only [h1, h107, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                · linarith only [h0, h109, h91, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                  · linarith only [h0, h111, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                    · linarith only [h1, h113, h95, hc01, hlam, hphi, u1elo2]
                    · linarith only [h0, h1, h113, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h116 | h116
    · rcases m.htr 0 1 4 (by decide) (by decide) with h117 | h117
      · rcases m.htr 0 1 5 (by decide) (by decide) with h118 | h118
        · linarith only [h0, h118, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h120 | h120
          · rcases m.htr 0 3 4 (by decide) (by decide) with h121 | h121
            · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
              · linarith only [h0, h116, h122, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                  · linarith only [h125, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                    · linarith only [h0, h116, h125, h127, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h116, h121, h125, h127, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h117, h120, h124, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
              · linarith only [h121, h131, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                  · linarith only [h134, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                    · linarith only [h0, h116, h121, h134, h136, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h131, h138, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h0, h117, h134, h140, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                          · linarith only [h0, h117, h133, h134, h136, h142, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                            · linarith only [h0, h117, h133, h134, h136, h138, h144, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                            · linarith only [h0, h117, h133, h134, h136, h144, hc23, hc35, hlam, hphi]
                · linarith only [h0, h120, h133, hlam]
          · linarith only [h0, h116, h120, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h149 | h149
        · linarith only [h117, h149, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h151 | h151
          · rcases m.htr 0 3 4 (by decide) (by decide) with h152 | h152
            · linarith only [h116, h117, h152, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
              · linarith only [h0, h116, h154, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                  · linarith only [h157, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                    · linarith only [h0, h116, h152, h157, h159, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                      · linarith only [h154, h161, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                        · linarith only [h163, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · linarith only [h116, h117, h163, hc13, hc45, hlam, hphi, ht34]
                · linarith only [h0, h116, h151, h156, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h116, h151, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
      · rcases m.htr 0 1 5 (by decide) (by decide) with h169 | h169
        · linarith only [h116, h169, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h171 | h171
          · rcases m.htr 0 3 4 (by decide) (by decide) with h172 | h172
            · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
              · linarith only [h0, h171, h173, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h176, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                      · linarith only [h175, h176, h179, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                        · linarith only [h116, h168, h175, h176, h181, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                            · linarith only [h0, h116, h171, h176, h179, h184, hc01, hc25, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                              · linarith only [h0, h116, h168, h176, h178, h181, h186, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                              · linarith only [h116, h168, h175, h176, h184, h186, hc14, hc45, hlam, hphi]
                          · linarith only [h116, h168, h178, h179, h183, hc23, hc35, hlam, hphi]
                    · linarith only [h116, h168, h172, h178, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h171, h175, hlam]
            · linarith only [h116, h168, h172, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
            · rcases m.htr 0 3 5 (by decide) (by decide) with h194 | h194
              · linarith only [h116, h194, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
                · linarith only [h0, h171, h196, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
                  · linarith only [h196, h198, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h201 | h201
                      · linarith only [h201, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                        · linarith only [h168, h203, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h206 | h206
                            · linarith only [h0, h168, h196, h200, h201, h206, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h168, h196, h200, h206, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h168, h196, h200, h205, hlam]
                    · linarith only [h0, h168, h193, h196, h200, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h116, h168, h193, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · linarith only [h0, h212, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h214 | h214
          · rcases m.htr 0 3 4 (by decide) (by decide) with h215 | h215
            · rcases m.htr 0 3 5 (by decide) (by decide) with h216 | h216
              · linarith only [h0, h214, h216, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h219, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h215, h216, h218, h219, h222, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                        · linarith only [h218, h219, h221, h224, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                            · linarith only [h168, h221, h222, h227, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                              · linarith only [h0, h168, h214, h219, h224, h226, h227, h229, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h214, h219, h226, h227, h229, hc34, hc45, hlam, hphi]
                          · linarith only [h215, h216, h226, hc23, hc35, hlam, hphi]
                    · linarith only [h116, h215, h221, hlam]
                · linarith only [h0, h214, h218, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
              · linarith only [h215, h235, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
                  · linarith only [h238, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
                    · linarith only [h116, h215, h237, h238, h240, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                      · linarith only [h235, h237, h238, h242, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                        · linarith only [h244, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                          · linarith only [h116, h240, h246, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                            · linarith only [h0, h116, h214, h238, h242, h248, hc01, hc25, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                              · linarith only [h168, h244, h250, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h116, h240, h250, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h214, h237, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h254 | h254
            · rcases m.htr 0 3 5 (by decide) (by decide) with h255 | h255
              · linarith only [h116, h255, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                · linarith only [h0, h214, h257, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                  · linarith only [h257, h259, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                      · linarith only [h254, h255, h262, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h264 | h264
                        · linarith only [h264, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h267 | h267
                            · linarith only [h0, h257, h262, h267, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h257, h267, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h254, h257, h266, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h254, h255, h261, hc13, hc35, hlam, hphi]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
              · linarith only [h254, h272, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
                · linarith only [h0, h214, h274, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
                  · linarith only [h276, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                    · linarith only [h116, h254, h278, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                      · linarith only [h272, h278, h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h282, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
                          · linarith only [h0, h274, h278, h284, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h274, h284, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
