import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_14_25_L_I_L_R_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h11, h13, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h11, h15, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · linarith only [h15, hlam, hphi, ht45, u4ehi2, u5elo4]
                      · linarith only [h10, h4, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · linarith only [h8, h9, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                        · linarith only [h20, h22, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h0, h24, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h20, h24, h8, hc23, hc34, hlam, hphi]
                      · linarith only [h21, hlam, hphi, ht45, u4ehi1, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                        · linarith only [h0, h1, h28, h29, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                          · linarith only [h20, h31, h5, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                            · linarith only [h0, h33, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h33, hlam, hphi, ht45, u4ehi2, u5elo4]
                      · linarith only [h28, h4, hlam, hphi, ht45, u4ehi1, u5elo0]
                · linarith only [h3, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                · linarith only [h0, h2, h38, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h3, h38, h5, hc23, hlam, hphi, ht34, ht45, u5elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
              · linarith only [h0, h1, h41, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h1, h43, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                              · linarith only [h0, h1, h45, h5, h51, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · linarith only [h51, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h0, h1, h45, h47, h5, h50, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h46, h49, h5, hlam]
                        · linarith only [h45, h48, h5, hlam]
                      · linarith only [h47, hlam, hphi, ht45, u4ehi1, u5elo4]
                    · linarith only [h45, h46, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                        · linarith only [h45, h59, h61, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                              · rcases h2bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  rcases p66_3 (m.d 0 2) (by simp) with h68 | h68
                                  · rcases p66_3 (m.d 1 2) (by simp) with h69 | h69
                                    · linarith only [h0, h69, hlam]
                                    · rcases p66_3 (m.d 2 3) (by simp) with h71 | h71
                                      · linarith only [h1, h71, hlam]
                                      · linarith only [h5, h71, hlam]
                                  · linarith only [h0, h68, hlam]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h0, h5, h59, h65, hc01, hlam, hphi, ht0b, ht45, ht5b, p66_1, u4ehi4]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h0, h41, h45, h59, h65, hc01, hlam, hphi, ht0b, ht45, ht5b, p66_1, u4ehi4]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  rcases p66_3 (m.d 0 2) (by simp) with h77 | h77
                                  · rcases p66_3 (m.d 1 2) (by simp) with h78 | h78
                                    · linarith only [h0, h78, hlam]
                                    · rcases p66_3 (m.d 2 3) (by simp) with h80 | h80
                                      · linarith only [h1, h80, hlam]
                                      · linarith only [h63, h80, hlam]
                                  · linarith only [h77, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h0, hlam, p66_1]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h5, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h41, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h43, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h1, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h61, hc12, hc34, hlam, hphi, ht23, p66_1]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h61, hlam, p66_1]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h43, h61, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u5ehi6]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h2, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  rcases p66_3 (m.d 0 2) (by simp) with h95 | h95
                                  · rcases p66_3 (m.d 1 2) (by simp) with h96 | h96
                                    · linarith only [h96, hlam, p66_0]
                                    · rcases p66_3 (m.d 2 3) (by simp) with h98 | h98
                                      · linarith only [h61, h98, hlam]
                                      · linarith only [h5, h98, hlam]
                                  · linarith only [h0, h95, hlam]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h0, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p66_1]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h0, h2, h43, h5, h59, h61, h65, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p66_1, u4ehi4]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h3, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h5, h59, h61, h65, hc12, hc34, hlam, hphi, ht23, ht45, p66_1, u4ehi4, u5elo2]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h63, hlam, p66_0]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [h64, hlam, p66_1]
                                · have p66_0 := h66c.1
                                  have p66_1 := h66c.2.1
                                  have p66_2 := h66c.2.2.1
                                  have p66_3 := h66c.2.2.2
                                  linarith only [hlam, p66_0]
                              · linarith only [h5, h59, h61, h65, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                            · linarith only [h41, h60, h64, hlam]
                          · linarith only [h5, h59, h63, hlam]
                      · linarith only [h60, hlam, hphi, ht45, u4ehi1, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                        · linarith only [h0, h1, h114, h115, h45, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h117 | h117
                          · linarith only [h115, h117, h5, h59, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h117, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h114, hlam, hphi, ht45, u4ehi1, u5elo4]
          · linarith only [h4, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h1, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h123 | h123
        · rcases m.htr 0 4 5 (by decide) (by decide) with h124 | h124
          · rcases m.htr 1 2 3 (by decide) (by decide) with h125 | h125
            · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
              · linarith only [h123, h126, h2, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                  · linarith only [h125, h126, h129, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                        · linarith only [h129, h131, h133, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                          · linarith only [h0, h125, h133, h135, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                          · linarith only [h0, h125, h131, h133, h135, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h132, hlam, hphi, ht45, u4ehi1, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                        · linarith only [h1, h140, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h125, h131, h142, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h145 | h145
                              · rcases h2bigk with h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c | h146c
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h140, h2, hc12, hc34, hlam, hphi, ht23, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h140, h2, hc23, hc34, hlam, hphi, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h2, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h140, h144, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p146_1, u4ehi4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h140, h2, hc23, hc34, hlam, hphi, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h126, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h0, h140, h144, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p146_1, u4ehi4]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h1, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h125, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h140, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h142, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h1, h140, hc23, hc34, hlam, hphi, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h125, h140, hc23, hc34, hlam, hphi, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  rcases p146_3 (m.d 0 2) (by simp) with h164 | h164
                                  · linarith only [h164, h2, hlam]
                                  · linarith only [h1, h164, hlam]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  rcases p146_3 (m.d 0 2) (by simp) with h168 | h168
                                  · linarith only [h168, h2, hlam]
                                  · linarith only [h123, h168, hlam]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h123, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h128, hlam, p146_0]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p146_1, u5elo2]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [h144, hlam, p146_1]
                                · have p146_0 := h146c.1
                                  have p146_1 := h146c.2.1
                                  have p146_2 := h146c.2.2.1
                                  have p146_3 := h146c.2.2.2
                                  linarith only [hlam, p146_0]
                              · linarith only [h0, h128, h140, h145, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                            · linarith only [h0, h128, h131, h139, h144, h2, hlam, hphi, u5ehi7, u5elo3]
                      · linarith only [h139, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h123, h128, h2, hc12, hc24, hlam, hphi]
            · linarith only [h1, h125, h2, hc12, hc24, hlam, hphi]
          · linarith only [h124, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h1, h123, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h183 | h183
      · rcases m.htr 0 2 5 (by decide) (by decide) with h184 | h184
        · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
          · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
            · linarith only [h1, h183, h185, h186, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
              · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h192 | h192
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                            · linarith only [h1, h183, h195, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h195, hlam, hphi, ht45, u4ehi2, u5elo4]
                          · linarith only [h0, h1, h189, h194, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h1, h189, h193, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h1, h183, h185, h192, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h186, h188, h191, hlam, hphi, ht45, u4ehi2, u5elo3]
                  · linarith only [h186, h188, h190, hlam]
                · linarith only [h188, h189, hlam, hphi, ht45, u4ehi2, u5elo2]
              · linarith only [h1, h183, h188, hc12, hc23, hlam, hphi]
          · linarith only [h185, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h183, h184, hlam, hphi, ht45, u4ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
        · rcases m.htr 0 4 5 (by decide) (by decide) with h208 | h208
          · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
            · linarith only [h0, h1, h209, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
              · linarith only [h0, h183, h211, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                              · rcases h2bigk with h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h183, h217, hc12, hc23, hlam, hphi, p221_1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h1, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h183, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h183, h217, h218, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, hlam, p221_1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h209, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h211, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h218, h220, hc01, hlam, hphi, ht0b, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h207, h218, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h213, h218, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h183, h207, h218, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  rcases p221_3 (m.d 0 2) (by simp) with h236 | h236
                                  · linarith only [h1, h236, hlam]
                                  · linarith only [h207, h236, hlam]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h0, h213, h218, h220, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h213, h218, h220, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p221_1, u4ehi4]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h217, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  rcases p221_3 (m.d 0 2) (by simp) with h243 | h243
                                  · linarith only [h183, h243, hlam]
                                  · linarith only [h207, h243, hlam]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h207, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h213, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h218, hlam, p221_0]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [h219, hlam, p221_1]
                                · have p221_0 := h221c.1
                                  have p221_1 := h221c.2.1
                                  have p221_2 := h221c.2.2.1
                                  have p221_3 := h221c.2.2.2
                                  linarith only [hlam, p221_0]
                              · linarith only [h220, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h216, h219, hlam, hphi, ht45, u4ehi2, u5elo1]
                          · linarith only [h0, h1, h213, h218, hlam, hphi, u5ehi7, u5elo3]
                        · linarith only [h0, h1, h213, h217, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h216, hlam, hphi, ht45, u4ehi1, u5elo4]
                    · linarith only [h214, h215, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h259 | h259
                        · linarith only [h209, h213, h214, h259, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h0, h1, h213, h259, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h209, h213, h214, h258, hlam, hphi, u5ehi7, u5elo4]
                    · linarith only [h209, h213, h257, hlam, hphi, u5ehi7, u5elo3]
                · linarith only [h1, h207, h213, hc12, hc23, hlam, hphi]
          · linarith only [h208, hlam, hphi, ht45, u4ehi0, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h266 | h266
          · rcases m.htr 1 2 3 (by decide) (by decide) with h267 | h267
            · linarith only [h0, h1, h267, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
              · linarith only [h0, h183, h269, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                · linarith only [h0, h207, h271, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h275 | h275
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h278 | h278
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                              · rcases h2bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h207, hc12, hlam, hphi, ht23, ht34, ht45, p280_1, u5elo2]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h1, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h183, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h207, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h0, hlam, p280_1]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h267, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h269, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h271, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  rcases p280_3 (m.d 0 2) (by simp) with h291 | h291
                                  · linarith only [h291, hlam, p280_0]
                                  · rcases p280_3 (m.d 1 2) (by simp) with h293 | h293
                                    · linarith only [h267, h293, hlam]
                                    · rcases p280_3 (m.d 2 3) (by simp) with h295 | h295
                                      · rcases p280_3 (m.d 2 4) (by simp) with h296 | h296
                                        · linarith only [h276, h296, hlam]
                                        · linarith only [h183, h296, hlam]
                                      · linarith only [h295, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  rcases p280_3 (m.d 0 2) (by simp) with h300 | h300
                                  · linarith only [h1, h300, hlam]
                                  · linarith only [h0, h300, hlam]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h269, h273, h279, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p280_1, u4ehi4]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h207, hc02, hc23, hlam, hphi, p280_1]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  rcases p280_3 (m.d 0 2) (by simp) with h306 | h306
                                  · linarith only [h306, hlam, p280_0]
                                  · rcases p280_3 (m.d 1 2) (by simp) with h308 | h308
                                    · linarith only [h269, h308, hlam]
                                    · rcases p280_3 (m.d 2 3) (by simp) with h310 | h310
                                      · rcases p280_3 (m.d 2 4) (by simp) with h311 | h311
                                        · rcases p280_3 (m.d 2 5) (by simp) with h312 | h312
                                          · linarith only [h278, h312, hlam]
                                          · linarith only [h207, h312, hlam]
                                        · linarith only [h311, hlam, p280_0]
                                      · linarith only [h1, h310, hlam]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  rcases p280_3 (m.d 0 2) (by simp) with h317 | h317
                                  · linarith only [h183, h317, hlam]
                                  · linarith only [h0, h317, hlam]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h276, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h0, h207, hc12, hc24, hlam, hphi, p280_1]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p280_1, u5elo2]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p280_1, u5elo2]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h277, hlam, p280_0]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [h278, hlam, p280_1]
                                · have p280_0 := h280c.1
                                  have p280_1 := h280c.2.1
                                  have p280_2 := h280c.2.2.1
                                  have p280_3 := h280c.2.2.2
                                  linarith only [hlam, p280_0]
                              · linarith only [h279, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h183, h207, h266, h278, hlam, hphi, ht45, u4ehi0, u5elo2]
                          · linarith only [h0, h1, h271, h274, h277, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                        · linarith only [h267, h273, h276, hlam]
                      · linarith only [h266, h275, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · linarith only [h273, h274, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                        · linarith only [h273, h334, h336, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                              · rcases h2bigk with h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h1, h336, hc12, hc34, hlam, hphi, ht23, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h1, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h183, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h207, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h0, hlam, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h267, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h269, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h271, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h336, hc02, hc34, hlam, hphi, ht23, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h336, hc12, hc34, hlam, hphi, ht23, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h336, hlam, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h207, h336, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p341_1, u5ehi5]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  rcases p341_3 (m.d 0 2) (by simp) with h357 | h357
                                  · linarith only [h357, hlam, p341_0]
                                  · rcases p341_3 (m.d 1 2) (by simp) with h359 | h359
                                    · linarith only [h269, h359, hlam]
                                    · rcases p341_3 (m.d 2 3) (by simp) with h361 | h361
                                      · linarith only [h336, h361, hlam]
                                      · linarith only [h1, h361, hlam]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  rcases p341_3 (m.d 0 2) (by simp) with h364 | h364
                                  · linarith only [h183, h364, hlam]
                                  · linarith only [h0, h364, hlam]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h267, h334, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p341_1, u5ehi8]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h0, h207, h336, hc12, hc34, hlam, hphi, ht23, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p341_1, u5elo2]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p341_1, u5elo2]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h338, hlam, p341_0]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [h339, hlam, p341_1]
                                · have p341_0 := h341c.1
                                  have p341_1 := h341c.2.1
                                  have p341_2 := h341c.2.2.1
                                  have p341_3 := h341c.2.2.2
                                  linarith only [hlam, p341_0]
                              · linarith only [h266, h267, h334, h336, h340, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                            · linarith only [h183, h207, h266, h339, hlam, hphi, ht45, u4ehi0, u5elo2]
                          · linarith only [h267, h334, h338, hlam]
                      · linarith only [h207, h266, h335, hlam, hphi, ht45, u4ehi1, u5elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                              · rcases h2bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h1, hc12, hc23, hlam, hphi, p384_1]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h1, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h183, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h207, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h0, hlam, p384_1]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h267, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h269, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h271, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  rcases p384_3 (m.d 0 2) (by simp) with h395 | h395
                                  · linarith only [h395, hlam, p384_0]
                                  · rcases p384_3 (m.d 1 2) (by simp) with h397 | h397
                                    · linarith only [h267, h397, hlam]
                                    · rcases p384_3 (m.d 2 3) (by simp) with h399 | h399
                                      · rcases p384_3 (m.d 2 4) (by simp) with h400 | h400
                                        · linarith only [h380, h400, hlam]
                                        · linarith only [h183, h400, hlam]
                                      · linarith only [h399, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  rcases p384_3 (m.d 0 2) (by simp) with h404 | h404
                                  · linarith only [h1, h404, hlam]
                                  · linarith only [h0, h404, hlam]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h273, h379, h380, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p384_1, u5ehi9]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h207, hc02, hc23, hlam, hphi, p384_1]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  rcases p384_3 (m.d 0 2) (by simp) with h410 | h410
                                  · linarith only [h410, hlam, p384_0]
                                  · rcases p384_3 (m.d 1 2) (by simp) with h412 | h412
                                    · linarith only [h269, h412, hlam]
                                    · rcases p384_3 (m.d 2 3) (by simp) with h414 | h414
                                      · rcases p384_3 (m.d 2 4) (by simp) with h415 | h415
                                        · rcases p384_3 (m.d 2 5) (by simp) with h416 | h416
                                          · linarith only [h382, h416, hlam]
                                          · linarith only [h207, h416, hlam]
                                        · linarith only [h415, hlam, p384_0]
                                      · linarith only [h1, h414, hlam]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  rcases p384_3 (m.d 0 2) (by simp) with h421 | h421
                                  · linarith only [h183, h421, hlam]
                                  · linarith only [h0, h421, hlam]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h380, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h267, h334, h381, hc12, hc24, hlam, hphi, p384_1]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p384_1, u5elo2]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p384_1, u5elo2]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h381, hlam, p384_0]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [h382, hlam, p384_1]
                                · have p384_0 := h384c.1
                                  have p384_1 := h384c.2.1
                                  have p384_2 := h384c.2.2.1
                                  have p384_3 := h384c.2.2.2
                                  linarith only [hlam, p384_0]
                              · linarith only [h273, h379, h383, hlam]
                            · linarith only [h382, hlam, hphi, ht45, u4ehi2, u5elo4]
                          · linarith only [h273, h379, h380, h381, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                          · linarith only [h267, h334, h380, h435, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1, h435, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h266, h379, hlam, hphi, ht45, u4ehi1, u5elo0]
          · linarith only [h266, hlam, hphi, ht45, u4ehi0, u5elo4]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h440 | h440
    · rcases m.htr 0 2 4 (by decide) (by decide) with h441 | h441
      · rcases m.htr 0 2 5 (by decide) (by decide) with h442 | h442
        · rcases m.htr 0 4 5 (by decide) (by decide) with h443 | h443
          · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
            · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
              · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h453 | h453
                              · linarith only [h440, h450, h453, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h453, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h452, hlam, hphi, ht45, u4ehi2, u5elo4]
                          · linarith only [h448, h450, h451, hlam, hphi, ht45, u4ehi3, u5elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
                          · linarith only [h444, h447, h450, h458, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h460 | h460
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                              · rcases h2bigk with h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h0, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  rcases p462_3 (m.d 0 2) (by simp) with h465 | h465
                                  · rcases p462_3 (m.d 1 2) (by simp) with h466 | h466
                                    · rcases p462_3 (m.d 2 3) (by simp) with h467 | h467
                                      · linarith only [h467, hlam, p462_0]
                                      · rcases p462_3 (m.d 2 4) (by simp) with h469 | h469
                                        · linarith only [h441, h469, hlam]
                                        · linarith only [h450, h469, hlam]
                                    · linarith only [h444, h466, hlam]
                                  · linarith only [h465, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h0, h460, hc12, hlam, hphi, ht01, ht0b, ht5b, p462_1, u5ehi9]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  rcases p462_3 (m.d 0 2) (by simp) with h475 | h475
                                  · rcases p462_3 (m.d 1 2) (by simp) with h476 | h476
                                    · rcases p462_3 (m.d 2 3) (by simp) with h477 | h477
                                      · linarith only [h440, h477, hlam]
                                      · rcases p462_3 (m.d 2 4) (by simp) with h479 | h479
                                        · linarith only [h441, h479, hlam]
                                        · linarith only [h460, h479, hlam]
                                    · linarith only [h446, h476, hlam]
                                  · linarith only [h475, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h441, h460, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p462_1, u4ehi4]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  rcases p462_3 (m.d 0 2) (by simp) with h486 | h486
                                  · linarith only [h0, h486, hlam]
                                  · linarith only [h440, h486, hlam]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h460, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p462_1, u4ehi4]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  rcases p462_3 (m.d 0 2) (by simp) with h490 | h490
                                  · linarith only [h0, h490, hlam]
                                  · linarith only [h442, h490, hlam]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h440, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h444, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h450, hlam, p462_1]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h458, hlam, p462_1]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h441, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h445, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  rcases p462_3 (m.d 0 2) (by simp) with h500 | h500
                                  · rcases p462_3 (m.d 1 2) (by simp) with h501 | h501
                                    · rcases p462_3 (m.d 2 3) (by simp) with h502 | h502
                                      · linarith only [h450, h502, hlam]
                                      · rcases p462_3 (m.d 2 4) (by simp) with h504 | h504
                                        · rcases p462_3 (m.d 2 5) (by simp) with h505 | h505
                                          · linarith only [h460, h505, hlam]
                                          · linarith only [h458, h505, hlam]
                                        · linarith only [h450, h504, hlam]
                                    · linarith only [h444, h501, hlam]
                                  · linarith only [h440, h500, hlam]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h441, h460, hc02, hlam, hphi, ht0b, ht45, ht5b, p462_1, u4ehi4]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h442, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h446, hlam, p462_0]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p462_1, u5elo2]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [h460, hlam, p462_1]
                                · have p462_0 := h462c.1
                                  have p462_1 := h462c.2.1
                                  have p462_2 := h462c.2.2.1
                                  have p462_3 := h462c.2.2.2
                                  linarith only [hlam, p462_0]
                              · linarith only [h450, h461, hlam, hphi, ht45, u4ehi2, u5elo4]
                            · linarith only [h443, h460, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h443, h449, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · linarith only [h447, h448, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                        · linarith only [h440, h447, h522, h524, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h526 | h526
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h528 | h528
                              · rcases h2bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h0, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h0, h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h0, h524, h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  rcases p529_3 (m.d 0 2) (by simp) with h534 | h534
                                  · rcases p529_3 (m.d 1 2) (by simp) with h535 | h535
                                    · rcases p529_3 (m.d 2 3) (by simp) with h536 | h536
                                      · linarith only [h440, h536, hlam]
                                      · linarith only [h526, h536, hlam]
                                    · linarith only [h446, h535, hlam]
                                  · linarith only [h534, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h440, h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h524, h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  rcases p529_3 (m.d 0 2) (by simp) with h545 | h545
                                  · linarith only [h0, h545, hlam]
                                  · linarith only [h442, h545, hlam]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h440, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h444, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h524, hlam, p529_1]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h441, h524, h526, h528, hc02, hlam, hphi, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h441, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h445, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h0, h441, h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h0, h441, h526, h528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p529_1, u4ehi4]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h442, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h446, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h526, hlam, p529_0]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [h527, hlam, p529_1]
                                · have p529_0 := h529c.1
                                  have p529_1 := h529c.2.1
                                  have p529_2 := h529c.2.2.1
                                  have p529_3 := h529c.2.2.2
                                  linarith only [hlam, p529_0]
                              · linarith only [h444, h447, h526, h528, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                            · linarith only [h443, h527, hlam, hphi, ht45, u4ehi2, u5elo0]
                          · linarith only [h447, h522, h526, hc23, hc34, hlam, hphi]
                      · linarith only [h443, h523, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                        · linarith only [h444, h522, h568, hlam, hphi, ht45, u4ehi3, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                          · linarith only [h444, h522, h570, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                              · rcases h2bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h0, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  rcases p574_3 (m.d 0 2) (by simp) with h577 | h577
                                  · rcases p574_3 (m.d 1 2) (by simp) with h578 | h578
                                    · rcases p574_3 (m.d 2 3) (by simp) with h579 | h579
                                      · linarith only [h579, hlam, p574_0]
                                      · rcases p574_3 (m.d 2 4) (by simp) with h581 | h581
                                        · linarith only [h441, h581, hlam]
                                        · linarith only [h568, h581, hlam]
                                    · linarith only [h444, h578, hlam]
                                  · linarith only [h577, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h0, h572, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi4]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  rcases p574_3 (m.d 0 2) (by simp) with h587 | h587
                                  · rcases p574_3 (m.d 1 2) (by simp) with h588 | h588
                                    · rcases p574_3 (m.d 2 3) (by simp) with h589 | h589
                                      · linarith only [h440, h589, hlam]
                                      · rcases p574_3 (m.d 2 4) (by simp) with h591 | h591
                                        · linarith only [h441, h591, hlam]
                                        · linarith only [h572, h591, hlam]
                                    · linarith only [h446, h588, hlam]
                                  · linarith only [h587, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h441, h572, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi4]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  rcases p574_3 (m.d 0 2) (by simp) with h598 | h598
                                  · linarith only [h0, h598, hlam]
                                  · linarith only [h440, h598, hlam]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h572, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi4]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  rcases p574_3 (m.d 0 2) (by simp) with h602 | h602
                                  · linarith only [h0, h602, hlam]
                                  · linarith only [h442, h602, hlam]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h440, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h444, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h568, hlam, p574_1]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h570, hlam, p574_1]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h441, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h445, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  rcases p574_3 (m.d 0 2) (by simp) with h612 | h612
                                  · rcases p574_3 (m.d 1 2) (by simp) with h613 | h613
                                    · rcases p574_3 (m.d 2 3) (by simp) with h614 | h614
                                      · linarith only [h568, h614, hlam]
                                      · rcases p574_3 (m.d 2 4) (by simp) with h616 | h616
                                        · rcases p574_3 (m.d 2 5) (by simp) with h617 | h617
                                          · linarith only [h572, h617, hlam]
                                          · linarith only [h570, h617, hlam]
                                        · linarith only [h568, h616, hlam]
                                    · linarith only [h444, h613, hlam]
                                  · linarith only [h440, h612, hlam]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h441, h572, hc02, hlam, hphi, ht0b, ht45, ht5b, p574_1, u4ehi4]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h442, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h446, hlam, p574_0]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p574_1, u5elo2]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [h572, hlam, p574_1]
                                · have p574_0 := h574c.1
                                  have p574_1 := h574c.2.1
                                  have p574_2 := h574c.2.2.1
                                  have p574_3 := h574c.2.2.2
                                  linarith only [hlam, p574_0]
                              · linarith only [h447, h573, hlam, hphi, ht45, u4ehi1, u5elo4]
                            · linarith only [h522, h567, h572, hlam, hphi, ht45, u4ehi2, u5elo3]
                      · linarith only [h567, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h0, h446, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h441, h445, hlam]
            · linarith only [h0, h440, h444, hlam]
          · linarith only [h443, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h440, h442, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h638 | h638
        · rcases m.htr 0 4 5 (by decide) (by decide) with h639 | h639
          · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
            · rcases m.htr 1 2 4 (by decide) (by decide) with h641 | h641
              · linarith only [h441, h638, h641, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h643 | h643
                · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
                  · linarith only [h640, h641, h644, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h647 | h647
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h648 | h648
                        · linarith only [h644, h646, h648, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
                          · linarith only [h0, h440, h641, h648, h650, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                          · linarith only [h640, h641, h646, h648, h650, hc23, hc34, hlam, hphi]
                      · linarith only [h639, h647, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h654 | h654
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h655 | h655
                        · linarith only [h0, h440, h641, h655, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h657 | h657
                          · linarith only [h640, h646, h657, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h659 | h659
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                              · rcases h2bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, h641, h655, hc23, hc34, hlam, hphi, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h441, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, h641, h655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p661_1, u5ehi7]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h641, h655, hc02, hc34, hlam, hphi, ht23, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h641, h655, hc23, hc34, hlam, hphi, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h641, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h641, h655, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p661_1, u4ehi4]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h440, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h640, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h655, hlam, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h657, hlam, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h638, h655, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p661_1, u4ehi4]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, h655, hc01, hc34, hlam, hphi, ht12, ht23, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  rcases p661_3 (m.d 0 2) (by simp) with h679 | h679
                                  · linarith only [h441, h679, hlam]
                                  · linarith only [h440, h679, hlam]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  rcases p661_3 (m.d 0 2) (by simp) with h683 | h683
                                  · linarith only [h441, h683, hlam]
                                  · linarith only [h638, h683, hlam]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h638, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h643, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p661_1, u5elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h659, hlam, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                              · linarith only [h0, h638, h641, h655, h660, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                            · linarith only [h0, h638, h641, h646, h654, h659, hlam, hphi, u5ehi7, u5elo3]
                      · linarith only [h654, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h0, h638, h643, hlam]
            · linarith only [h0, h440, h640, hlam]
          · linarith only [h639, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h440, h638, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h698 | h698
      · rcases m.htr 0 2 5 (by decide) (by decide) with h699 | h699
        · rcases m.htr 0 4 5 (by decide) (by decide) with h700 | h700
          · rcases m.htr 1 2 3 (by decide) (by decide) with h701 | h701
            · linarith only [h440, h698, h700, h701, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h703 | h703
              · rcases m.htr 1 2 5 (by decide) (by decide) with h704 | h704
                · rcases m.htr 1 3 4 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h706 | h706
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h707 | h707
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h708 | h708
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h709 | h709
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h710 | h710
                            · linarith only [h0, h698, h701, h710, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                            · linarith only [h710, hlam, hphi, ht45, u4ehi2, u5elo4]
                          · linarith only [h0, h699, h701, h709, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h699, h701, h708, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h0, h698, h700, h701, h707, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h698, h701, h706, hlam, hphi, ht45, u4ehi0, u5elo3]
                  · linarith only [h701, h703, h705, hlam]
                · linarith only [h0, h698, h700, h704, hlam, hphi, ht45, u4ehi4, u5elo2]
              · linarith only [h0, h698, h703, hlam]
          · linarith only [h700, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h698, h699, hlam, hphi, ht45, u4ehi2, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h722 | h722
        · rcases m.htr 0 4 5 (by decide) (by decide) with h723 | h723
          · rcases m.htr 1 2 3 (by decide) (by decide) with h724 | h724
            · linarith only [h440, h722, h724, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h726 | h726
              · linarith only [h698, h722, h726, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
                · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h730 | h730
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h733 | h733
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h734 | h734
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h735 | h735
                              · rcases h2bigk with h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c | h736c
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h0, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h440, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h698, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h0, h726, h732, h733, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p736_1, u4ehi4]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h726, h732, hc02, hc23, hlam, hphi, p736_1]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h724, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h726, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h726, h732, h733, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p736_1, u4ehi4]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h722, h733, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p736_1, u4ehi4]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p736_1]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h698, h722, h733, h735, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p736_1, u4ehi4]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  rcases p736_3 (m.d 0 2) (by simp) with h751 | h751
                                  · linarith only [h440, h751, hlam]
                                  · linarith only [h722, h751, hlam]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h722, h733, h735, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p736_1, u4ehi4]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h0, h722, h733, h735, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p736_1, u4ehi4]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h732, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  rcases p736_3 (m.d 0 2) (by simp) with h758 | h758
                                  · linarith only [h698, h758, hlam]
                                  · linarith only [h722, h758, hlam]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h722, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h728, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h733, hlam, p736_0]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [h734, hlam, p736_1]
                                · have p736_0 := h736c.1
                                  have p736_1 := h736c.2.1
                                  have p736_2 := h736c.2.2.1
                                  have p736_3 := h736c.2.2.2
                                  linarith only [hlam, p736_0]
                              · linarith only [h735, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h734, hlam, hphi, ht45, u4ehi2, u5elo4]
                          · linarith only [h440, h733, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h722, h724, h732, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h723, h731, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · linarith only [h729, h730, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h772 | h772
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h773 | h773
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h774 | h774
                        · linarith only [h0, h722, h724, h729, h774, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                        · linarith only [h440, h722, h774, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h723, h773, hlam, hphi, ht45, u4ehi1, u5elo0]
                    · linarith only [h0, h722, h724, h772, hlam, hphi, u5ehi7, u5elo3]
                · linarith only [h0, h722, h728, hlam]
          · linarith only [h723, hlam, hphi, ht45, u4ehi0, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
          · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
            · rcases m.htr 1 2 4 (by decide) (by decide) with h783 | h783
              · rcases m.htr 1 2 5 (by decide) (by decide) with h784 | h784
                · rcases m.htr 1 3 4 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h787 | h787
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h788 | h788
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h789 | h789
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h790 | h790
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h791 | h791
                              · linarith only [h782, h788, h791, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h791, hlam, hphi, ht45, u4ehi3, u5elo4]
                            · linarith only [h698, h781, h790, hlam]
                          · linarith only [h698, h788, h789, hlam, hphi, ht45, u4ehi0, u5elo3]
                        · linarith only [h0, h440, h785, h788, hc01, hc13, hlam, hphi]
                      · linarith only [h698, h781, h783, h787, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h785, h786, hlam, hphi, ht45, u4ehi3, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h800 | h800
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h801 | h801
                        · linarith only [h0, h722, h784, h785, h799, h801, hc01, hc23, hlam, hphi, ht12, u5ehi8, u5elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h803 | h803
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h804 | h804
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h805 | h805
                              · rcases h2bigk with h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c | h806c
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h440, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h698, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h722, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  rcases p806_3 (m.d 0 2) (by simp) with h812 | h812
                                  · linarith only [h0, h812, hlam]
                                  · rcases p806_3 (m.d 1 2) (by simp) with h814 | h814
                                    · rcases p806_3 (m.d 2 3) (by simp) with h815 | h815
                                      · linarith only [h782, h815, hlam]
                                      · linarith only [h440, h815, hlam]
                                    · linarith only [h0, h814, hlam]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h722, h784, h803, h805, hc01, hc12, hlam, hphi, ht45, p806_1, u4ehi4, u5elo1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h698, hc01, hc12, hlam, hphi, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h722, hc01, hc12, hlam, hphi, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h782, h785, hc01, hc34, hlam, hphi, ht12, ht23, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h782, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h801, hlam, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h722, h782, h785, hc01, hc34, hlam, hphi, ht12, ht23, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h783, hc01, hc12, hlam, hphi, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h783, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h440, h783, hc01, hc12, hlam, hphi, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h722, h783, hc01, hc12, hlam, hphi, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h0, h784, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p806_1, u5elo1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h784, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h803, hlam, p806_0]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [h804, hlam, p806_1]
                                · have p806_0 := h806c.1
                                  have p806_1 := h806c.2.1
                                  have p806_2 := h806c.2.2.1
                                  have p806_3 := h806c.2.2.2
                                  linarith only [hlam, p806_0]
                              · linarith only [h781, h782, h785, h803, h805, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                            · linarith only [h698, h781, h804, hlam]
                          · linarith only [h0, h440, h803, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h698, h781, h783, h800, hlam]
                    · linarith only [h0, h440, h782, h799, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h698, h781, h783, h784, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h0, h440, h782, h783, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h845 | h845
              · linarith only [h0, h698, h782, h845, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h847 | h847
                · linarith only [h0, h722, h782, h847, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h847, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h781, hlam, hphi, ht45, u4ehi0, u5elo4]

end R2N4
