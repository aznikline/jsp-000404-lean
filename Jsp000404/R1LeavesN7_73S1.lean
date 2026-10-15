import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_I_L_I_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
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
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · linarith only [h13, h14, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h13, h17, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                                · linarith only [h0, h19, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · linarith only [h12, h19, h2, hc24, hlam, hphi, u4elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h23, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · linarith only [h22, h23, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h10, h12, h22, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h10, h11, h6, hc34, hlam, hphi, ht45, u5elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h10, h28, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                            · linarith only [h28, h31, h6, h7, hc34, hlam, hphi, ht45, u5elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h33 | h33
                              · linarith only [h28, h33, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                                · linarith only [h0, h35, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · linarith only [h10, h30, h35, h5, hc24, hlam, hphi, u4elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                            · linarith only [h28, h38, h6, h7, hc34, hlam, hphi, ht45, u5elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h28, h38, h40, hc13, hlam, hphi, ht34, u4elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h30, h42, h8, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                                  · linarith only [h30, h44, h5, hc14, hlam, hphi, u4elo0]
                                  · linarith only [h10, h44, h7, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h7, h8, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                                · linarith only [h49, h56, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                                · linarith only [h2, h53, h56, hc24, hlam, hphi, u4elo0]
                              · linarith only [h50, h55, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                            · linarith only [h54, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                                · linarith only [h49, h53, h63, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                                  · linarith only [h49, h53, h61, h65, hlam]
                                  · rcases h1bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h50, h62, hc01, hlam, hphi, ht0b, ht5b, p67_1, u5ehi8]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h50, h62, h7, hc01, hlam, hphi, ht0b, ht5b, p67_1, u5ehi8]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      rcases p67_3 (m.d 0 1) (by simp) with h71 | h71
                                      · rcases p67_3 (m.d 1 2) (by simp) with h72 | h72
                                        · linarith only [h0, h72, hlam]
                                        · linarith only [h49, h72, hlam]
                                      · linarith only [h71, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      rcases p67_3 (m.d 0 1) (by simp) with h76 | h76
                                      · rcases p67_3 (m.d 1 2) (by simp) with h77 | h77
                                        · linarith only [h0, h77, hlam]
                                        · linarith only [h50, h77, hlam]
                                      · linarith only [h76, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h0, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h7, hlam, p67_1]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      rcases p67_3 (m.d 0 1) (by simp) with h84 | h84
                                      · rcases p67_3 (m.d 1 2) (by simp) with h85 | h85
                                        · rcases p67_3 (m.d 1 3) (by simp) with h86 | h86
                                          · rcases p67_3 (m.d 1 4) (by simp) with h87 | h87
                                            · linarith only [h49, h87, hlam]
                                            · rcases p67_3 (m.d 1 5) (by simp) with h89 | h89
                                              · linarith only [h50, h89, hlam]
                                              · linarith only [h53, h89, hlam]
                                          · linarith only [h51, h86, hlam]
                                        · linarith only [h49, h85, hlam]
                                      · linarith only [h2, h84, hlam]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p67_1, u5ehi6]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h1, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h1, h49, h61, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p67_1]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      rcases p67_3 (m.d 0 1) (by simp) with h99 | h99
                                      · rcases p67_3 (m.d 1 2) (by simp) with h100 | h100
                                        · linarith only [h100, h7, hlam]
                                        · linarith only [h100, h49, hlam]
                                      · linarith only [h2, h99, hlam]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h1, h50, h62, hc01, hlam, hphi, ht0b, ht5b, p67_1, u5ehi8]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h2, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h49, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h51, hlam, p67_1]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h53, hlam, p67_1]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h3, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h50, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h52, hlam, p67_0]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [h49, h61, hc34, hlam, hphi, ht45, p67_1, u5elo1]
                                    · have p67_0 := h67c.1
                                      have p67_1 := h67c.2.1
                                      have p67_2 := h67c.2.2.1
                                      have p67_3 := h67c.2.2.2
                                      linarith only [hlam, p67_0]
                              · linarith only [h50, h62, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                            · linarith only [h50, h61, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h50, h52, h6, h7, hlam, hphi, u5ehi7, u5elo0]
                      · linarith only [h50, h51, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi7]
                    · linarith only [h49, h50, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h120, h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h123 | h123
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h128 | h128
                                  · linarith only [h1, h122, h128, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                  · linarith only [h124, h128, h4, h49, hc34, hlam, hphi, u4elo0]
                                · linarith only [h124, h127, h49, hlam]
                              · linarith only [h124, h126, h4, h49, h6, h7, hc12, hlam, hphi, ht23, ht34, u4elo0, u5ehi9, u5elo0]
                            · linarith only [h122, h124, h125, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h136 | h136
                                · linarith only [h124, h136, h4, hc14, hlam, hphi, u4elo0]
                                · linarith only [h136, h49, hc12, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h123, h135, h7, hlam]
                            · linarith only [h122, h123, h124, h134, h7, hlam, hphi, u5ehi8, u5elo4]
                        · linarith only [h122, h123, h6, hc34, hlam, hphi, ht45, u5elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                        · linarith only [h122, h142, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                                  · rcases h1bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      rcases p149_3 (m.d 0 1) (by simp) with h151 | h151
                                      · rcases p149_3 (m.d 1 2) (by simp) with h152 | h152
                                        · linarith only [h152, hlam, p149_0]
                                        · rcases p149_3 (m.d 1 3) (by simp) with h154 | h154
                                          · linarith only [h1, h154, hlam]
                                          · linarith only [h154, h7, hlam]
                                      · linarith only [h151, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      rcases p149_3 (m.d 0 1) (by simp) with h158 | h158
                                      · rcases p149_3 (m.d 1 2) (by simp) with h159 | h159
                                        · linarith only [h0, h159, hlam]
                                        · rcases p149_3 (m.d 1 3) (by simp) with h161 | h161
                                          · linarith only [h161, hlam, p149_0]
                                          · rcases p149_3 (m.d 1 4) (by simp) with h163 | h163
                                            · linarith only [h163, h2, hlam]
                                            · linarith only [h122, h163, hlam]
                                      · linarith only [h158, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h144, hc01, hlam, hphi, ht0b, ht5b, p149_1, u5ehi9]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      rcases p149_3 (m.d 0 1) (by simp) with h168 | h168
                                      · rcases p149_3 (m.d 1 2) (by simp) with h169 | h169
                                        · linarith only [h0, h169, hlam]
                                        · rcases p149_3 (m.d 1 3) (by simp) with h171 | h171
                                          · linarith only [h1, h171, hlam]
                                          · rcases p149_3 (m.d 1 4) (by simp) with h173 | h173
                                            · linarith only [h173, h2, hlam]
                                            · linarith only [h144, h173, hlam]
                                      · linarith only [h168, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h7, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h49, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h120, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h1, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h142, h6, hc12, hlam, hphi, ht23, ht34, ht45, p149_1, u5elo0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h122, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h142, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h2, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h4, h49, hc12, hlam, hphi, ht23, ht34, p149_1, u4elo0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h122, h145, h4, hc13, hlam, hphi, ht34, p149_1, u4elo0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h122, h145, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p149_1, u4elo0, u5ehi6]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h3, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p149_1, u5elo1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h122, h142, h144, h145, h4, h6, h7, hc12, hlam, hphi, ht23, ht34, p149_1, u4elo0, u5ehi9, u5elo0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h144, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                  · linarith only [h122, h144, h148, hlam]
                                · linarith only [h122, h144, h145, h147, hlam]
                              · linarith only [h122, h144, h145, h146, h6, hlam, hphi, u5ehi9, u5elo0]
                            · linarith only [h145, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h203 | h203
                                · linarith only [h144, h203, h4, hc14, hlam, hphi, u4elo0]
                                · linarith only [h203, h49, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                              · linarith only [h122, h201, h202, h6, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                            · linarith only [h201, h7, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
              · linarith only [h209, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                      · linarith only [h1, h209, h214, h5, hc04, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                        · linarith only [h209, h214, h216, hc03, hlam, hphi, ht34, u4elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h218 | h218
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                            · linarith only [h1, h2, h209, h211, h218, h219, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                              · linarith only [h1, h209, h211, h221, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                                · linarith only [h0, h212, h223, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · linarith only [h2, h218, h223, h5, hc24, hlam, hphi, u4elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                            · linarith only [h1, h209, h211, h226, h5, hc04, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                              · linarith only [h209, h226, h228, hc03, hlam, hphi, ht34, u4elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                                · linarith only [h212, h218, h230, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                                  · linarith only [h218, h232, hc14, hlam, hphi, u4elo3]
                                  · linarith only [h1, h211, h232, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h211, h213, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h211, h212, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
                  · linarith only [h1, h209, h211, h237, hc24, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
                    · linarith only [h1, h209, h211, h239, hlam, hphi, u5ehi7, u5elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                      · linarith only [h1, h209, h241, h5, hc04, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                        · linarith only [h1, h209, h243, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                            · linarith only [h246, h4, h5, hlam]
                            · linarith only [h211, h246, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                            · linarith only [h249, h4, h5, hlam]
                            · linarith only [h211, h249, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h252 | h252
            · rcases m.htr 0 3 5 (by decide) (by decide) with h253 | h253
              · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                · linarith only [h0, h254, h4, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h256, h4, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h258, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h262 | h262
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                                  · linarith only [h1, h260, h266, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                                  · linarith only [h2, h262, h266, h4, hc34, hlam, hphi, u4elo2]
                                · linarith only [h2, h262, h265, h4, hlam]
                              · linarith only [h2, h253, h254, h262, h264, h4, hc12, hlam, hphi, ht23, ht34, u4elo2, u5ehi9, u5elo0]
                            · linarith only [h254, h260, h262, h263, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h274 | h274
                                · linarith only [h256, h262, h274, hc12, hlam, hphi, ht23, ht34, u4elo2]
                                · linarith only [h274, h4, hc02, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h254, h261, h273, hlam]
                            · linarith only [h254, h260, h261, h272, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi8]
                        · linarith only [h260, h261, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
                        · linarith only [h252, h260, h280, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h282 | h282
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h286 | h286
                                  · rcases h1bigk with h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      rcases p287_3 (m.d 0 1) (by simp) with h289 | h289
                                      · rcases p287_3 (m.d 1 2) (by simp) with h290 | h290
                                        · linarith only [h290, hlam, p287_0]
                                        · rcases p287_3 (m.d 1 3) (by simp) with h292 | h292
                                          · linarith only [h1, h292, hlam]
                                          · linarith only [h254, h292, hlam]
                                      · linarith only [h289, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      rcases p287_3 (m.d 0 1) (by simp) with h296 | h296
                                      · rcases p287_3 (m.d 1 2) (by simp) with h297 | h297
                                        · linarith only [h0, h297, hlam]
                                        · rcases p287_3 (m.d 1 3) (by simp) with h299 | h299
                                          · linarith only [h299, hlam, p287_0]
                                          · rcases p287_3 (m.d 1 4) (by simp) with h301 | h301
                                            · linarith only [h2, h301, hlam]
                                            · linarith only [h260, h301, hlam]
                                      · linarith only [h296, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h282, hc01, hlam, hphi, ht0b, ht5b, p287_1, u5ehi9]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      rcases p287_3 (m.d 0 1) (by simp) with h306 | h306
                                      · rcases p287_3 (m.d 1 2) (by simp) with h307 | h307
                                        · linarith only [h0, h307, hlam]
                                        · rcases p287_3 (m.d 1 3) (by simp) with h309 | h309
                                          · linarith only [h1, h309, hlam]
                                          · rcases p287_3 (m.d 1 4) (by simp) with h311 | h311
                                            · linarith only [h2, h311, hlam]
                                            · linarith only [h282, h311, hlam]
                                      · linarith only [h306, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h0, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h254, hlam, p287_1]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h256, hlam, p287_1]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h258, hlam, p287_1]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h1, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h253, h280, hc12, hlam, hphi, ht23, ht34, ht45, p287_1, u5elo0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h260, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h280, hlam, p287_1]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h2, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h2, h4, hc12, hlam, hphi, ht23, ht34, p287_1, u4elo2]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h252, h260, h4, hc13, hlam, hphi, ht34, p287_1, u4elo2]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h252, h260, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p287_1, u4elo2, u5ehi6]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h3, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p287_1, u5elo1]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h252, h253, h254, h260, h280, h282, h4, hc12, hlam, hphi, ht23, ht34, p287_1, u4elo2, u5ehi9, u5elo0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [h282, hlam, p287_0]
                                    · have p287_0 := h287c.1
                                      have p287_1 := h287c.2.1
                                      have p287_2 := h287c.2.2.1
                                      have p287_3 := h287c.2.2.2
                                      linarith only [hlam, p287_0]
                                  · linarith only [h260, h282, h286, hlam]
                                · linarith only [h252, h260, h282, h285, h4, hlam]
                              · linarith only [h253, h260, h282, h283, h284, hlam, hphi, u5ehi9, u5elo0]
                            · linarith only [h252, h254, h283, h4, hc12, hlam, hphi, ht23, ht34, u4elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h340 | h340
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                                · linarith only [h282, h341, hc14, hlam, hphi, u4elo2]
                                · linarith only [h341, h4, hc02, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h254, h260, h339, h340, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h252, h254, h339, hc12, hlam, hphi, ht23, ht34, u4elo0]
              · linarith only [h252, h253, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
              · linarith only [h252, h347, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                · linarith only [h0, h349, h4, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h351 | h351
                  · linarith only [h1, h347, h349, h351, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h353 | h353
                    · linarith only [h0, h353, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                      · linarith only [h1, h347, h355, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h357 | h357
                        · linarith only [h1, h347, h357, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h359 | h359
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h361 | h361
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                                  · rcases h1bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 1) (by simp) with h366 | h366
                                      · rcases p364_3 (m.d 1 2) (by simp) with h367 | h367
                                        · linarith only [h367, hlam, p364_0]
                                        · rcases p364_3 (m.d 1 3) (by simp) with h369 | h369
                                          · linarith only [h1, h369, hlam]
                                          · linarith only [h349, h369, hlam]
                                      · linarith only [h366, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 1) (by simp) with h373 | h373
                                      · rcases p364_3 (m.d 1 2) (by simp) with h374 | h374
                                        · linarith only [h0, h374, hlam]
                                        · rcases p364_3 (m.d 1 3) (by simp) with h376 | h376
                                          · linarith only [h376, hlam, p364_0]
                                          · rcases p364_3 (m.d 1 4) (by simp) with h378 | h378
                                            · linarith only [h2, h378, hlam]
                                            · linarith only [h355, h378, hlam]
                                      · linarith only [h373, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h359, hc01, hlam, hphi, ht0b, ht5b, p364_1, u5ehi9]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      rcases p364_3 (m.d 0 1) (by simp) with h383 | h383
                                      · rcases p364_3 (m.d 1 2) (by simp) with h384 | h384
                                        · linarith only [h0, h384, hlam]
                                        · rcases p364_3 (m.d 1 3) (by simp) with h386 | h386
                                          · linarith only [h1, h386, hlam]
                                          · rcases p364_3 (m.d 1 4) (by simp) with h388 | h388
                                            · linarith only [h2, h388, hlam]
                                            · linarith only [h359, h388, hlam]
                                      · linarith only [h383, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h0, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h349, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h351, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h353, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h1, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h1, h2, h252, h347, h359, h360, h361, hc12, hlam, hphi, ht23, ht34, p364_1, u4elo2, u5ehi9, u5elo2]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h355, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h357, hlam, p364_1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h2, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h2, h252, h360, hc12, hlam, hphi, ht23, ht34, p364_1, u4elo2]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h2, h252, h360, hc13, hlam, hphi, ht34, p364_1, u4elo2]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h2, h252, h360, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p364_1, u4elo2, u5ehi6]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h3, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p364_1, u5elo1]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h2, h252, h3, h349, h359, h360, hc12, hlam, hphi, ht23, ht34, p364_1, u4elo2, u5ehi9, u5elo0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [h359, hlam, p364_0]
                                    · have p364_0 := h364c.1
                                      have p364_1 := h364c.2.1
                                      have p364_2 := h364c.2.2.1
                                      have p364_3 := h364c.2.2.2
                                      linarith only [hlam, p364_0]
                                  · linarith only [h2, h252, h359, h363, hlam]
                                · linarith only [h2, h252, h359, h360, h362, hlam]
                              · linarith only [h2, h252, h359, h360, h361, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                            · linarith only [h349, h360, hc12, hlam, hphi, ht23, ht34, u4elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h418 | h418
                                · linarith only [h359, h418, hc14, hlam, hphi, u4elo2]
                                · linarith only [h4, h418, hc02, hlam, hphi, ht23, ht34, u4elo4]
                              · linarith only [h1, h252, h349, h416, h417, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h349, h416, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h425 | h425
      · rcases m.htr 0 1 5 (by decide) (by decide) with h426 | h426
        · rcases m.htr 0 2 4 (by decide) (by decide) with h427 | h427
          · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
            · rcases m.htr 0 3 5 (by decide) (by decide) with h429 | h429
              · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                · linarith only [h0, h1, h430, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
                    · linarith only [h0, h1, h430, h433, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · linarith only [h432, h433, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h1, h427, h430, h432, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h427, h429, hc24, hlam, hphi, ht45, u5elo3]
            · linarith only [h1, h426, h428, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi6]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h439 | h439
            · rcases m.htr 0 3 5 (by decide) (by decide) with h440 | h440
              · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                · linarith only [h0, h427, h441, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                  · linarith only [h0, h427, h443, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                    · linarith only [h0, h427, h445, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                          · linarith only [h1, h425, h449, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                                · linarith only [h449, h453, hc14, hlam, hphi, u4elo2]
                                · linarith only [h0, h427, h453, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1, h441, h452, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1, h426, h441, h448, h451, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h1, h426, h448, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                      · linarith only [h1, h426, h447, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
              · linarith only [h1, h426, h440, hlam, hphi, u5ehi6, u5elo3]
            · linarith only [h1, h426, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi6]
        · linarith only [h0, h426, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h425, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h464 | h464
    · rcases m.htr 0 1 4 (by decide) (by decide) with h465 | h465
      · rcases m.htr 0 1 5 (by decide) (by decide) with h466 | h466
        · rcases m.htr 0 2 4 (by decide) (by decide) with h467 | h467
          · rcases m.htr 0 3 4 (by decide) (by decide) with h468 | h468
            · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
              · rcases m.htr 1 2 3 (by decide) (by decide) with h470 | h470
                · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
                        · linarith only [h0, h464, h474, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · linarith only [h473, h474, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                        · linarith only [h0, h464, h468, h473, h477, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h479 | h479
                          · linarith only [h0, h464, h468, h473, h479, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h481 | h481
                            · linarith only [h470, h473, h481, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
                              · linarith only [h470, h477, h483, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h485 | h485
                                · linarith only [h471, h479, h485, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h487 | h487
                                  · linarith only [h0, h464, h468, h479, h487, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h470, h473, h487, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h472, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h464, h469, h471, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h0, h464, h469, h470, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h468, h469, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h494 | h494
              · linarith only [h468, h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
                · rcases m.htr 1 2 4 (by decide) (by decide) with h497 | h497
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
                      · linarith only [h464, h494, h499, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h501 | h501
                        · linarith only [h464, h494, h501, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
                          · linarith only [h0, h465, h503, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                            · linarith only [h464, h468, h496, h505, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                              · linarith only [h464, h494, h496, h507, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                                · linarith only [h497, h503, h509, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h511 | h511
                                  · linarith only [h503, h511, hc14, hlam, hphi, u4elo3]
                                  · linarith only [h468, h511, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h498, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h466, h467, h497, hc02, hlam, hphi, ht0b, ht5b, u5ehi6]
                · linarith only [h0, h466, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h466, h467, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi6]
        · linarith only [h465, h466, hc14, hlam, hphi, ht45, u5elo1]
      · linarith only [h464, h465, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h520 | h520
      · rcases m.htr 0 1 5 (by decide) (by decide) with h521 | h521
        · rcases m.htr 0 2 4 (by decide) (by decide) with h522 | h522
          · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
            · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
              · rcases m.htr 1 2 3 (by decide) (by decide) with h525 | h525
                · rcases m.htr 1 2 4 (by decide) (by decide) with h526 | h526
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h527 | h527
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h528 | h528
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h529 | h529
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h530 | h530
                          · linarith only [h464, h520, h525, h530, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h534 | h534
                                · linarith only [h526, h530, h534, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                                  · linarith only [h526, h530, h532, h536, hlam]
                                  · rcases h1bigk with h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h0, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h464, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      rcases p538_3 (m.d 0 1) (by simp) with h542 | h542
                                      · rcases p538_3 (m.d 1 2) (by simp) with h543 | h543
                                        · rcases p538_3 (m.d 1 3) (by simp) with h544 | h544
                                          · rcases p538_3 (m.d 1 4) (by simp) with h545 | h545
                                            · linarith only [h545, hlam, p538_0]
                                            · rcases p538_3 (m.d 1 5) (by simp) with h547 | h547
                                              · linarith only [h521, h547, hlam]
                                              · linarith only [h530, h547, hlam]
                                          · linarith only [h528, h544, hlam]
                                        · linarith only [h526, h543, hlam]
                                      · linarith only [h542, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h464, h525, h527, h533, hc12, hlam, hphi, ht01, ht0b, ht5b, p538_1, u5ehi8]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h521, h527, h533, hc12, hlam, hphi, ht01, ht0b, ht5b, p538_1, u5ehi8]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h464, hc01, hc12, hlam, hphi, p538_1]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      rcases p538_3 (m.d 0 1) (by simp) with h557 | h557
                                      · linarith only [h0, h557, hlam]
                                      · linarith only [h520, h557, hlam]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      rcases p538_3 (m.d 0 1) (by simp) with h560 | h560
                                      · linarith only [h0, h560, hlam]
                                      · linarith only [h521, h560, hlam]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h521, h525, h527, h533, hc12, hlam, hphi, ht01, ht0b, ht5b, p538_1, u5ehi8]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h525, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      rcases p538_3 (m.d 0 1) (by simp) with h566 | h566
                                      · linarith only [h464, h566, hlam]
                                      · linarith only [h520, h566, hlam]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      rcases p538_3 (m.d 0 1) (by simp) with h569 | h569
                                      · linarith only [h464, h569, hlam]
                                      · linarith only [h521, h569, hlam]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h520, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h526, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h528, hlam, p538_1]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h530, hlam, p538_1]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h521, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h527, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [h529, hlam, p538_0]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [hc14, hlam, hphi, ht45, p538_1, u5elo1]
                                    · have p538_0 := h538c.1
                                      have p538_1 := h538c.2.1
                                      have p538_2 := h538c.2.2.1
                                      have p538_3 := h538c.2.2.2
                                      linarith only [hlam, p538_0]
                              · linarith only [h532, h533, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h528, h530, h532, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h464, h521, h529, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                      · linarith only [h464, h521, h523, h527, h528, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h0, h527, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h464, h521, h525, h526, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h521, h525, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h523, h524, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h464, h521, h523, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi6]
          · linarith only [h0, h521, h522, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi6]
        · linarith only [h520, h521, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h593 | h593
        · linarith only [h520, h593, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi6]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h595 | h595
          · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
            · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
              · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h602 | h602
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                  · linarith only [h598, h604, h607, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                                  · linarith only [h520, h595, h606, h607, hc34, hlam, hphi, u4elo1]
                                · linarith only [h603, h606, hc24, hlam, hphi, u4elo1]
                              · linarith only [h604, h605, hc34, hlam, hphi, ht45, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
                              · linarith only [h520, h596, h604, h612, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi8]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h615 | h615
                                  · rcases h1bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h0, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h464, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h520, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h593, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      rcases p616_3 (m.d 0 1) (by simp) with h622 | h622
                                      · linarith only [h622, hlam, p616_0]
                                      · rcases p616_3 (m.d 1 2) (by simp) with h624 | h624
                                        · rcases p616_3 (m.d 1 3) (by simp) with h625 | h625
                                          · linarith only [h598, h625, hlam]
                                          · linarith only [h464, h625, hlam]
                                        · linarith only [h624, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h464, h596, h604, h614, hc12, hlam, hphi, ht01, ht0b, ht5b, p616_1, u5ehi9]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h520, h596, h604, h614, hc12, hlam, hphi, ht01, ht0b, ht5b, p616_1, u5ehi9]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h593, hc01, hc12, hlam, hphi, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      rcases p616_3 (m.d 0 1) (by simp) with h633 | h633
                                      · linarith only [h633, hlam, p616_0]
                                      · rcases p616_3 (m.d 1 2) (by simp) with h635 | h635
                                        · rcases p616_3 (m.d 1 3) (by simp) with h636 | h636
                                          · rcases p616_3 (m.d 1 4) (by simp) with h637 | h637
                                            · linarith only [h601, h637, hlam]
                                            · linarith only [h520, h637, hlam]
                                          · linarith only [h636, hlam, p616_0]
                                        · linarith only [h0, h635, hlam]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h598, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h520, h596, h604, h614, hc13, hlam, hphi, ht01, ht0b, ht5b, p616_1, u5ehi9]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h593, h598, hc01, hc12, hlam, hphi, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p616_1, u4elo1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h599, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h601, hlam, p616_1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h593, hc01, hlam, hphi, ht12, ht23, ht34, p616_1, u4elo1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p616_1, u5elo1]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h600, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h602, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [h603, hlam, p616_0]
                                    · have p616_0 := h616c.1
                                      have p616_1 := h616c.2.1
                                      have p616_2 := h616c.2.2.1
                                      have p616_3 := h616c.2.2.2
                                      linarith only [hlam, p616_0]
                                  · linarith only [h604, h614, h615, hlam]
                                · linarith only [h603, h614, hc24, hlam, hphi, u4elo1]
                          · linarith only [h520, h603, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h464, h602, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h464, h596, h597, h601, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi8]
                    · linarith only [h0, h600, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h464, h597, h598, h599, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi8]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h667 | h667
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h669 | h669
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h670 | h670
                                · linarith only [h0, h595, h598, h670, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                                · linarith only [h667, h670, hc24, hlam, hphi, u4elo1]
                              · linarith only [h597, h598, h664, h669, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                            · linarith only [h598, h663, h667, h668, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                          · linarith only [h520, h667, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h464, h597, h666, hlam]
                      · linarith only [h464, h596, h597, h665, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi8]
                    · linarith only [h520, h663, h664, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h663, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h596, h597, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h681 | h681
              · linarith only [h596, h681, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h683 | h683
                · rcases m.htr 1 2 4 (by decide) (by decide) with h684 | h684
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h686 | h686
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h689 | h689
                            · linarith only [h464, h596, h683, h689, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h691 | h691
                              · linarith only [h464, h681, h689, h691, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                                  · rcases h1bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h0, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h464, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h520, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h593, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      rcases p695_3 (m.d 0 1) (by simp) with h701 | h701
                                      · linarith only [h701, hlam, p695_0]
                                      · rcases p695_3 (m.d 1 2) (by simp) with h703 | h703
                                        · rcases p695_3 (m.d 1 3) (by simp) with h704 | h704
                                          · linarith only [h683, h704, hlam]
                                          · linarith only [h464, h704, hlam]
                                        · linarith only [h703, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h464, hc01, hc12, hlam, hphi, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h520, hc01, hc12, hlam, hphi, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h464, h681, h687, hc01, hc12, hlam, hphi, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      rcases p695_3 (m.d 0 1) (by simp) with h712 | h712
                                      · linarith only [h712, hlam, p695_0]
                                      · rcases p695_3 (m.d 1 2) (by simp) with h714 | h714
                                        · rcases p695_3 (m.d 1 3) (by simp) with h715 | h715
                                          · rcases p695_3 (m.d 1 4) (by simp) with h716 | h716
                                            · linarith only [h686, h716, hlam]
                                            · linarith only [h520, h716, hlam]
                                          · linarith only [h715, hlam, p695_0]
                                        · linarith only [h0, h714, hlam]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h683, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h595, h596, h686, h693, hc13, hlam, hphi, ht01, ht0b, ht5b, p695_1, u5ehi9]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h464, h681, h683, h687, hc01, hc12, hlam, hphi, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p695_1, u4elo1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h684, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h686, hlam, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h464, h681, h687, hc01, hlam, hphi, ht12, ht23, ht34, p695_1, u4elo1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p695_1, u5elo1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h685, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h687, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h688, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                  · linarith only [h595, h596, h693, h694, hlam]
                                · linarith only [h688, h693, hc24, hlam, hphi, u4elo1]
                          · linarith only [h520, h688, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h464, h687, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h464, h686, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h685, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h684, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h744 | h744
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h745 | h745
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h746 | h746
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h747 | h747
                            · linarith only [h0, h464, h595, h596, h683, h747, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h683, h747, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h520, h746, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h464, h745, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h683, h743, h744, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi7]
                    · linarith only [h520, h742, h743, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h595, h742, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h755 | h755
            · rcases m.htr 0 3 5 (by decide) (by decide) with h756 | h756
              · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
                · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h759 | h759
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h761 | h761
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h762 | h762
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h763 | h763
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h764 | h764
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h765 | h765
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
                                  · linarith only [h757, h763, h766, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                                  · linarith only [h758, h765, h766, hc34, hlam, hphi, u4elo1]
                                · linarith only [h0, h595, h765, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h763, h764, hc34, hlam, hphi, ht45, u5elo3]
                            · linarith only [h595, h755, h763, hlam]
                          · linarith only [h520, h762, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h464, h756, h761, hlam]
                      · linarith only [h464, h755, h756, h760, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi8]
                    · linarith only [h0, h759, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h464, h756, h757, h758, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi8]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
                  · linarith only [h0, h595, h757, h777, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h777, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h755, h756, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h781 | h781
              · linarith only [h755, h781, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
                · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h785 | h785
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
                            · linarith only [h464, h755, h783, h789, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h791 | h791
                              · linarith only [h781, h786, h789, h791, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi5]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h793 | h793
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h794 | h794
                                  · rcases h1bigk with h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h0, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h464, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h520, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h593, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      rcases p795_3 (m.d 0 1) (by simp) with h801 | h801
                                      · linarith only [h801, hlam, p795_0]
                                      · rcases p795_3 (m.d 1 2) (by simp) with h803 | h803
                                        · rcases p795_3 (m.d 1 3) (by simp) with h804 | h804
                                          · linarith only [h783, h804, hlam]
                                          · linarith only [h464, h804, hlam]
                                        · linarith only [h803, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h464, hc01, hc12, hlam, hphi, p795_1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h520, hc01, hc12, hlam, hphi, p795_1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h464, h781, h787, hc01, hc12, hlam, hphi, p795_1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      rcases p795_3 (m.d 0 1) (by simp) with h812 | h812
                                      · linarith only [h812, hlam, p795_0]
                                      · rcases p795_3 (m.d 1 2) (by simp) with h814 | h814
                                        · rcases p795_3 (m.d 1 3) (by simp) with h815 | h815
                                          · rcases p795_3 (m.d 1 4) (by simp) with h816 | h816
                                            · linarith only [h786, h816, hlam]
                                            · linarith only [h520, h816, hlam]
                                          · linarith only [h815, hlam, p795_0]
                                        · linarith only [h0, h814, hlam]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h783, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h464, h781, h786, h787, h789, h793, hc01, hc13, hlam, hphi, p795_1, u5ehi9, u5elo1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h464, h781, h783, h787, hc01, hc12, hlam, hphi, p795_1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p795_1, u4elo1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h784, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h786, hlam, p795_1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h464, h781, h787, hc01, hlam, hphi, ht12, ht23, ht34, p795_1, u4elo1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p795_1, u5elo1]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h785, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h787, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [h788, hlam, p795_0]
                                    · have p795_0 := h795c.1
                                      have p795_1 := h795c.2.1
                                      have p795_2 := h795c.2.2.1
                                      have p795_3 := h795c.2.2.2
                                      linarith only [hlam, p795_0]
                                  · linarith only [h789, h793, h794, hlam]
                                · linarith only [h0, h595, h793, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h520, h788, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h464, h787, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h464, h786, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h785, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h464, h783, h784, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h842 | h842
                  · linarith only [h0, h595, h783, h842, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h842, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

end R2N4
