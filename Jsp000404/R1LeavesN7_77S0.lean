import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_I_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h4, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h1, h11, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h13, h4, h7, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                        · linarith only [h11, h15, h17, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h17, h7, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h3, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h1, h23, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h1, h22, h26, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h22, h25, h26, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h22, h25, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h2, h22, h30, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h0, h1, h32, h36, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h1, h33, h35, h36, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                        · linarith only [h0, h1, h32, h35, h39, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h2bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            rcases p41_3 (m.d 0 2) (by simp) with h43 | h43
                            · rcases p41_3 (m.d 1 2) (by simp) with h44 | h44
                              · linarith only [h0, h44, hlam]
                              · rcases p41_3 (m.d 2 3) (by simp) with h46 | h46
                                · linarith only [h1, h46, hlam]
                                · linarith only [h4, h46, hlam]
                            · linarith only [h0, h43, hlam]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h32, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1, u3ehi3]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            rcases p41_3 (m.d 0 2) (by simp) with h51 | h51
                            · rcases p41_3 (m.d 1 2) (by simp) with h52 | h52
                              · linarith only [h0, h52, hlam]
                              · rcases p41_3 (m.d 2 3) (by simp) with h54 | h54
                                · linarith only [h1, h54, hlam]
                                · linarith only [h33, h54, hlam]
                            · linarith only [h51, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            rcases p41_3 (m.d 0 2) (by simp) with h58 | h58
                            · rcases p41_3 (m.d 1 2) (by simp) with h59 | h59
                              · linarith only [h0, h59, hlam]
                              · rcases p41_3 (m.d 2 3) (by simp) with h61 | h61
                                · linarith only [h1, h61, hlam]
                                · linarith only [h34, h61, hlam]
                            · linarith only [h58, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h0, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h4, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h22, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h30, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h1, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            rcases p41_3 (m.d 0 2) (by simp) with h71 | h71
                            · rcases p41_3 (m.d 1 2) (by simp) with h72 | h72
                              · linarith only [h72, hlam, p41_0]
                              · rcases p41_3 (m.d 2 3) (by simp) with h74 | h74
                                · rcases p41_3 (m.d 2 4) (by simp) with h75 | h75
                                  · linarith only [h33, h75, hlam]
                                  · linarith only [h22, h75, hlam]
                                · linarith only [h74, hlam, p41_0]
                            · linarith only [h0, h71, hlam]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h22, hc12, hc23, hlam, hphi, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h0, h1, h22, h35, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h2, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h35, hc12, hc45, hlam, hphi, ht23, ht34, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h33, hlam, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h35, hlam, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h3, hlam, p41_0]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            rcases p41_3 (m.d 0 2) (by simp) with h89 | h89
                            · rcases p41_3 (m.d 1 2) (by simp) with h90 | h90
                              · linarith only [h90, hlam, p41_0]
                              · rcases p41_3 (m.d 2 3) (by simp) with h92 | h92
                                · rcases p41_3 (m.d 2 4) (by simp) with h93 | h93
                                  · linarith only [h35, h93, hlam]
                                  · linarith only [h22, h93, hlam]
                                · linarith only [h4, h92, hlam]
                            · linarith only [h0, h89, hlam]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h34, hlam, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [h0, h22, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1]
                          · have p41_0 := h41c.1
                            have p41_1 := h41c.2.1
                            have p41_2 := h41c.2.2.1
                            have p41_3 := h41c.2.2.2
                            linarith only [hlam, p41_0]
                    · linarith only [h32, h34, h4, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h32, h33, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h0, h1, h103, h32, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                    · linarith only [h103, h105, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                        · rcases h2bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            rcases p109_3 (m.d 0 2) (by simp) with h111 | h111
                            · rcases p109_3 (m.d 1 2) (by simp) with h112 | h112
                              · linarith only [h0, h112, hlam]
                              · rcases p109_3 (m.d 2 3) (by simp) with h114 | h114
                                · linarith only [h1, h114, hlam]
                                · linarith only [h114, h4, hlam]
                            · linarith only [h0, h111, hlam]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            rcases p109_3 (m.d 0 2) (by simp) with h118 | h118
                            · rcases p109_3 (m.d 1 2) (by simp) with h119 | h119
                              · linarith only [h0, h119, hlam]
                              · rcases p109_3 (m.d 2 3) (by simp) with h121 | h121
                                · linarith only [h121, hlam, p109_0]
                                · rcases p109_3 (m.d 2 4) (by simp) with h123 | h123
                                  · linarith only [h123, h2, hlam]
                                  · linarith only [h103, h123, hlam]
                            · linarith only [h118, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, h107, hc01, hlam, hphi, ht0b, ht5b, p109_1, u5ehi4]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            rcases p109_3 (m.d 0 2) (by simp) with h128 | h128
                            · rcases p109_3 (m.d 1 2) (by simp) with h129 | h129
                              · linarith only [h0, h129, hlam]
                              · rcases p109_3 (m.d 2 3) (by simp) with h131 | h131
                                · linarith only [h1, h131, hlam]
                                · rcases p109_3 (m.d 2 4) (by simp) with h133 | h133
                                  · linarith only [h133, h2, hlam]
                                  · linarith only [h107, h133, hlam]
                            · linarith only [h128, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h4, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h22, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h30, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h1, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h103, hc12, hc34, hlam, hphi, ht23, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h103, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h105, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h2, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            rcases p109_3 (m.d 0 2) (by simp) with h148 | h148
                            · rcases p109_3 (m.d 1 2) (by simp) with h149 | h149
                              · linarith only [h149, hlam, p109_0]
                              · rcases p109_3 (m.d 2 3) (by simp) with h151 | h151
                                · linarith only [h103, h151, hlam]
                                · linarith only [h151, h4, hlam]
                            · linarith only [h0, h148, hlam]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p109_1, u3ehi2]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h0, h105, h2, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h3, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            rcases p109_3 (m.d 0 2) (by simp) with h159 | h159
                            · rcases p109_3 (m.d 1 2) (by simp) with h160 | h160
                              · linarith only [h160, hlam, p109_0]
                              · rcases p109_3 (m.d 2 3) (by simp) with h162 | h162
                                · linarith only [h105, h162, hlam]
                                · linarith only [h162, h4, hlam]
                            · linarith only [h0, h159, hlam]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h4, hc12, hc25, hlam, hphi, p109_1]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [h107, hlam, p109_0]
                          · have p109_0 := h109c.1
                            have p109_1 := h109c.2.1
                            have p109_2 := h109c.2.2.1
                            have p109_3 := h109c.2.2.2
                            linarith only [hlam, p109_0]
                        · linarith only [h108, h32, hc45, hlam, hphi, ht34, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                        · linarith only [h107, h170, h22, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h170, h32, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
          · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
            · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
              · linarith only [h175, h3, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h177 | h177
                · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                  · linarith only [h0, h173, h178, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h173, h177, h178, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                  · linarith only [h1, h181, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                    · linarith only [h0, h174, h181, h183, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h174, h181, h183, h3, hc35, hlam, hphi, u3ehi2]
            · linarith only [h173, h174, h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h1, h173, h3, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h188 | h188
        · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
          · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
            · linarith only [h188, h190, h2, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
              · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                · linarith only [h189, h190, h193, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                  · linarith only [h0, h189, h193, h195, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h1, h195, h2, hc34, hlam, hphi, u3ehi2]
              · linarith only [h188, h189, h192, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h1, h189, h2, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
          · rcases m.htr 1 2 4 (by decide) (by decide) with h201 | h201
            · linarith only [h2, h201, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
              · linarith only [h0, h188, h203, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                · linarith only [h200, h201, h205, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · linarith only [h1, h205, h207, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h1, h2, h207, hc34, hlam, hphi, u3ehi2]
          · linarith only [h1, h2, h200, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h211 | h211
      · rcases m.htr 0 2 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
          · linarith only [h1, h212, h213, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
            · rcases m.htr 1 2 5 (by decide) (by decide) with h216 | h216
              · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
                · rcases m.htr 2 3 4 (by decide) (by decide) with h218 | h218
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h219 | h219
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h220 | h220
                      · linarith only [h0, h1, h215, h220, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h222 | h222
                        · linarith only [h218, h220, h222, hlam]
                        · rcases h2bigk with h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, hc12, hc23, hlam, hphi, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h1, h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p224_1, u3ehi4]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h0, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h213, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h0, h218, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h0, h1, h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p224_1, u3ehi4]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p224_1, u0ehi1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h215, h218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            rcases p224_3 (m.d 0 2) (by simp) with h238 | h238
                            · linarith only [h1, h238, hlam]
                            · linarith only [h211, h238, hlam]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            rcases p224_3 (m.d 0 2) (by simp) with h241 | h241
                            · linarith only [h1, h241, hlam]
                            · linarith only [h212, h241, hlam]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h211, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h215, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h218, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h220, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h212, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h216, hlam, p224_0]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h219, hlam, p224_1]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [h0, h216, h218, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1, u3ehi3]
                          · have p224_0 := h224c.1
                            have p224_1 := h224c.2.1
                            have p224_2 := h224c.2.2.1
                            have p224_3 := h224c.2.2.2
                            linarith only [hlam, p224_0]
                    · linarith only [h0, h1, h216, h219, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h1, h216, h217, h218, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h213, h215, h217, hlam]
              · linarith only [h1, h212, h215, h216, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h1, h211, h215, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
          · linarith only [h1, h259, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
            · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
              · linarith only [h0, h212, h262, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h267 | h267
                      · linarith only [h0, h212, h261, h266, h267, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h212, h261, h265, h267, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h0, h1, h261, h265, h266, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h265, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h259, h261, h264, hlam]
            · linarith only [h1, h211, h261, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h274 | h274
        · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
          · linarith only [h1, h274, h275, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
            · linarith only [h0, h211, h277, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
              · rcases m.htr 1 3 4 (by decide) (by decide) with h280 | h280
                · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h283 | h283
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                        · rcases h2bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h211, h279, h281, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u3ehi4]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h1, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h211, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h211, h281, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u3ehi4]
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
                            linarith only [h275, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h277, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h0, h282, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1, u3ehi4]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p285_1, u0ehi1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h279, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u3ehi4]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h211, h274, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u3ehi4]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            rcases p285_3 (m.d 0 2) (by simp) with h300 | h300
                            · linarith only [h1, h300, hlam]
                            · linarith only [h274, h300, hlam]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h0, h279, h282, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u3ehi4]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h279, h282, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p285_1, u3ehi4]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h281, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            rcases p285_3 (m.d 0 2) (by simp) with h307 | h307
                            · linarith only [h211, h307, hlam]
                            · linarith only [h274, h307, hlam]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h274, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h279, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h282, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h283, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                        · linarith only [h0, h279, h283, h284, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h211, h279, h283, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h0, h211, h279, h281, h282, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h1, h279, h281, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                  · linarith only [h275, h279, h280, h319, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h1, h279, h319, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h1, h274, h279, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
          · linarith only [h1, h323, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h325 | h325
            · linarith only [h0, h211, h325, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
              · linarith only [h0, h274, h327, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h333 | h333
                        · rcases h2bigk with h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h274, h330, h332, hc12, hc23, hlam, hphi, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h1, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h211, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h274, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h0, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h323, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h325, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h327, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p334_1, u0ehi1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 2) (by simp) with h346 | h346
                            · linarith only [h1, h346, hlam]
                            · linarith only [h0, h346, hlam]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h211, hc23, hlam, hphi, ht01, ht12, p334_1, u0ehi1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h274, hc23, hlam, hphi, ht01, ht12, p334_1, u0ehi1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p334_1, u0ehi1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 2) (by simp) with h353 | h353
                            · linarith only [h211, h353, hlam]
                            · linarith only [h0, h353, hlam]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h330, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h274, h330, hc23, hlam, hphi, ht01, ht12, p334_1, u0ehi1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p334_1, u0ehi1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 2) (by simp) with h360 | h360
                            · linarith only [h274, h360, hlam]
                            · linarith only [h0, h360, hlam]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h331, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h332, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                        · rcases h2bigk with h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h1, hc12, hc23, hlam, hphi, p366_1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h1, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h211, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h274, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h0, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h323, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h325, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h327, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p366_1, u0ehi1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            rcases p366_3 (m.d 0 2) (by simp) with h378 | h378
                            · linarith only [h1, h378, hlam]
                            · linarith only [h0, h378, hlam]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h332, h333, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p366_1, u3ehi3]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h274, hc23, hlam, hphi, ht01, ht12, p366_1, u0ehi1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p366_1, u0ehi1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            rcases p366_3 (m.d 0 2) (by simp) with h385 | h385
                            · linarith only [h211, h385, hlam]
                            · linarith only [h0, h385, hlam]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h330, hlam, p366_1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h274, h330, hc23, hlam, hphi, ht01, ht12, p366_1, u0ehi1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p366_1, u0ehi1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            rcases p366_3 (m.d 0 2) (by simp) with h392 | h392
                            · linarith only [h274, h392, hlam]
                            · linarith only [h0, h392, hlam]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h331, hlam, p366_1]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [h332, hlam, p366_0]
                          · have p366_0 := h366c.1
                            have p366_1 := h366c.2.1
                            have p366_2 := h366c.2.2.1
                            have p366_3 := h366c.2.2.2
                            linarith only [hlam, p366_0]
                      · linarith only [h211, h332, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                    · linarith only [h1, h331, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h1, h329, h330, hc13, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h403 | h403
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
                        · rcases h2bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h274, h403, hc12, hc24, hlam, hphi, p405_1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h1, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h211, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h274, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h0, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h323, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h325, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h327, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p405_1, u0ehi1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            rcases p405_3 (m.d 0 2) (by simp) with h417 | h417
                            · linarith only [h1, h417, hlam]
                            · linarith only [h0, h417, hlam]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h211, hc23, hlam, hphi, ht01, ht12, p405_1, u0ehi1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h274, hc23, hlam, hphi, ht01, ht12, p405_1, u0ehi1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p405_1, u0ehi1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            rcases p405_3 (m.d 0 2) (by simp) with h424 | h424
                            · linarith only [h211, h424, hlam]
                            · linarith only [h0, h424, hlam]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h401, hlam, p405_1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h274, h401, hc23, hlam, hphi, ht01, ht12, p405_1, u0ehi1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht12, p405_1, u0ehi1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            rcases p405_3 (m.d 0 2) (by simp) with h431 | h431
                            · linarith only [h274, h431, hlam]
                            · linarith only [h0, h431, hlam]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h402, hlam, p405_1]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [h403, hlam, p405_0]
                          · have p405_0 := h405c.1
                            have p405_1 := h405c.2.1
                            have p405_2 := h405c.2.2.1
                            have p405_3 := h405c.2.2.2
                            linarith only [hlam, p405_0]
                        · linarith only [h329, h404, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h211, h403, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                    · linarith only [h1, h402, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h1, h401, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h441 | h441
    · rcases m.htr 0 2 4 (by decide) (by decide) with h442 | h442
      · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
        · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
          · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
            · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
              · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                        · linarith only [h441, h448, h451, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h441, h448, h450, h451, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                        · linarith only [h0, h441, h448, h450, h454, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h0, hlam, p456_1]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h0, h448, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u3ehi3]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            rcases p456_3 (m.d 0 2) (by simp) with h460 | h460
                            · rcases p456_3 (m.d 1 2) (by simp) with h461 | h461
                              · rcases p456_3 (m.d 2 3) (by simp) with h462 | h462
                                · linarith only [h441, h462, hlam]
                                · linarith only [h448, h462, hlam]
                              · linarith only [h445, h461, hlam]
                            · linarith only [h460, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            rcases p456_3 (m.d 0 2) (by simp) with h467 | h467
                            · rcases p456_3 (m.d 1 2) (by simp) with h468 | h468
                              · rcases p456_3 (m.d 2 3) (by simp) with h469 | h469
                                · linarith only [h441, h469, hlam]
                                · linarith only [h449, h469, hlam]
                              · linarith only [h446, h468, hlam]
                            · linarith only [h467, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p456_1, u0ehi1]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h449, h454, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u3ehi3]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            rcases p456_3 (m.d 0 2) (by simp) with h477 | h477
                            · linarith only [h0, h477, hlam]
                            · linarith only [h442, h477, hlam]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            rcases p456_3 (m.d 0 2) (by simp) with h480 | h480
                            · linarith only [h0, h480, hlam]
                            · linarith only [h443, h480, hlam]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h441, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h444, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h441, h448, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p456_1, u3ehi3]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h0, h441, h448, h450, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u3ehi3]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h442, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h445, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h448, hlam, p456_1]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h450, hlam, p456_1]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h443, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h446, hlam, p456_0]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h449, hlam, p456_1]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [h0, h443, h448, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p456_1, u3ehi3]
                          · have p456_0 := h456c.1
                            have p456_1 := h456c.2.1
                            have p456_2 := h456c.2.2.1
                            have p456_3 := h456c.2.2.2
                            linarith only [hlam, p456_0]
                    · linarith only [h448, h449, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                    · linarith only [h444, h447, h448, h499, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h502 | h502
                        · rcases h2bigk with h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h0, hlam, p503_1]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            rcases p503_3 (m.d 0 2) (by simp) with h506 | h506
                            · rcases p503_3 (m.d 1 2) (by simp) with h507 | h507
                              · rcases p503_3 (m.d 2 3) (by simp) with h508 | h508
                                · linarith only [h508, hlam, p503_0]
                                · rcases p503_3 (m.d 2 4) (by simp) with h510 | h510
                                  · linarith only [h442, h510, hlam]
                                  · linarith only [h448, h510, hlam]
                              · linarith only [h444, h507, hlam]
                            · linarith only [h506, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h0, h501, hc12, hlam, hphi, ht01, ht0b, ht5b, p503_1, u5ehi4]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            rcases p503_3 (m.d 0 2) (by simp) with h516 | h516
                            · rcases p503_3 (m.d 1 2) (by simp) with h517 | h517
                              · rcases p503_3 (m.d 2 3) (by simp) with h518 | h518
                                · linarith only [h441, h518, hlam]
                                · rcases p503_3 (m.d 2 4) (by simp) with h520 | h520
                                  · linarith only [h442, h520, hlam]
                                  · linarith only [h501, h520, hlam]
                              · linarith only [h446, h517, hlam]
                            · linarith only [h516, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p503_1, u0ehi1]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            rcases p503_3 (m.d 0 2) (by simp) with h527 | h527
                            · linarith only [h0, h527, hlam]
                            · linarith only [h441, h527, hlam]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h501, hc12, hlam, hphi, ht01, ht0b, ht5b, p503_1, u5ehi4]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            rcases p503_3 (m.d 0 2) (by simp) with h531 | h531
                            · linarith only [h0, h531, hlam]
                            · linarith only [h443, h531, hlam]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h441, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h444, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h448, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h499, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h442, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h445, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h442, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p503_1, u3ehi2]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h444, h447, h448, h499, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p503_1, u3ehi2]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h443, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h446, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h0, h443, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p503_1, u3ehi2]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [h501, hlam, p503_0]
                          · have p503_0 := h503c.1
                            have p503_1 := h503c.2.1
                            have p503_2 := h503c.2.2.1
                            have p503_3 := h503c.2.2.2
                            linarith only [hlam, p503_0]
                        · linarith only [h448, h502, hc45, hlam, hphi, ht34, u3ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h550 | h550
                        · linarith only [h444, h447, h448, h501, h550, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h448, h550, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                  · linarith only [h444, h447, h553, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                    · linarith only [h444, h447, h555, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                        · rcases h2bigk with h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h0, hlam, p559_1]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            rcases p559_3 (m.d 0 2) (by simp) with h562 | h562
                            · rcases p559_3 (m.d 1 2) (by simp) with h563 | h563
                              · rcases p559_3 (m.d 2 3) (by simp) with h564 | h564
                                · linarith only [h564, hlam, p559_0]
                                · rcases p559_3 (m.d 2 4) (by simp) with h566 | h566
                                  · linarith only [h442, h566, hlam]
                                  · linarith only [h553, h566, hlam]
                              · linarith only [h444, h563, hlam]
                            · linarith only [h562, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h557, hc02, hlam, hphi, ht0b, ht5b, p559_1, u5ehi4]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            rcases p559_3 (m.d 0 2) (by simp) with h572 | h572
                            · rcases p559_3 (m.d 1 2) (by simp) with h573 | h573
                              · rcases p559_3 (m.d 2 3) (by simp) with h574 | h574
                                · linarith only [h441, h574, hlam]
                                · rcases p559_3 (m.d 2 4) (by simp) with h576 | h576
                                  · linarith only [h442, h576, hlam]
                                  · linarith only [h557, h576, hlam]
                              · linarith only [h446, h573, hlam]
                            · linarith only [h572, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [hc12, hlam, hphi, ht01, p559_1, u0ehi1]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            rcases p559_3 (m.d 0 2) (by simp) with h583 | h583
                            · linarith only [h0, h583, hlam]
                            · linarith only [h441, h583, hlam]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h557, hc12, hlam, hphi, ht01, ht0b, ht5b, p559_1, u5ehi4]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            rcases p559_3 (m.d 0 2) (by simp) with h587 | h587
                            · linarith only [h0, h587, hlam]
                            · linarith only [h443, h587, hlam]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h441, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h444, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h553, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h555, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h442, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h445, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h442, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p559_1, u3ehi2]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h0, h442, h555, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p559_1, u3ehi2]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h443, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h446, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h0, h443, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p559_1, u3ehi2]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [h557, hlam, p559_0]
                          · have p559_0 := h559c.1
                            have p559_1 := h559c.2.1
                            have p559_2 := h559c.2.2.1
                            have p559_3 := h559c.2.2.2
                            linarith only [hlam, p559_0]
                        · linarith only [h444, h447, h558, hc45, hlam, hphi, ht34, u3ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h606 | h606
                        · linarith only [h553, h557, h606, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h444, h447, h606, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h443, h446, hc02, hlam, hphi, u0ehi0]
            · linarith only [h0, h445, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h444, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
          · rcases m.htr 1 2 4 (by decide) (by decide) with h613 | h613
            · rcases m.htr 1 2 5 (by decide) (by decide) with h614 | h614
              · linarith only [h441, h443, h614, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h614, hc25, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h442, h613, hc02, hlam, hphi, u0ehi0]
          · linarith only [h0, h612, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h619 | h619
        · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
          · rcases m.htr 1 2 4 (by decide) (by decide) with h621 | h621
            · linarith only [h441, h442, h621, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h621, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h441, h620, hc02, hlam, hphi, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h625 | h625
          · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
            · linarith only [h441, h442, h626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h626, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h441, h625, hc02, hlam, hphi, u0ehi0]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h630 | h630
      · rcases m.htr 0 2 5 (by decide) (by decide) with h631 | h631
        · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
          · linarith only [h441, h631, h632, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · linarith only [h0, h632, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
          · linarith only [h441, h630, h635, hc12, hlam, hphi, ht01, u0ehi3]
          · linarith only [h0, h635, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h638 | h638
        · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
          · linarith only [h441, h638, h639, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · linarith only [h0, h639, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
          · linarith only [h441, h642, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h642, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
