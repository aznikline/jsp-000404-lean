import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_IR_L_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
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
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h1, h10, h12, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                          · linarith only [h0, h14, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h14, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h17, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h1, h17, h19, h4, h5, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h21, h7, h9, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h0, h1, h17, h23, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h17, h23, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h6, h7, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                · linarith only [h28, h6, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h1, h30, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                            · linarith only [h0, h1, h33, h36, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h1, h28, h32, h33, h36, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h28, h32, h35, hlam]
                        · linarith only [h34, h6, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h33, h6, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                          · linarith only [h28, h32, h42, h44, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h1, h28, h4, h44, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                        · linarith only [h42, h43, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h42, h6, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h0, h2, h5, h50, h52, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h49, h54, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h4, h5, h54, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h3, h49, h51, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h49, h50, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                · linarith only [h49, h59, hc23, hlam, hphi, u2ehi3]
                · linarith only [h2, h5, h59, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
            · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
              · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                      · linarith only [h0, h4, h63, h67, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                        · linarith only [h1, h4, h69, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h0, h64, h71, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h4, h62, h67, h71, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h4, h62, h64, h66, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h3, h63, h65, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h63, h64, hc24, hlam, hphi, u2ehi2]
              · linarith only [h1, h4, h63, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                    · linarith only [h0, h4, h62, h79, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                      · linarith only [h1, h4, h62, h83, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h1, h4, h62, h85, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                          · linarith only [h0, h4, h62, h79, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                            · linarith only [h1, h4, h62, h89, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1, h4, h89, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h3, h78, h80, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h78, h79, hc24, hlam, hphi, u2ehi2]
              · linarith only [h1, h4, h78, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h1, h3, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h97 | h97
      · linarith only [h1, h97, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h99 | h99
        · linarith only [h1, h99, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
          · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
            · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
              · linarith only [h0, h1, h103, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
                · linarith only [h0, h105, h97, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                  · linarith only [h0, h107, h99, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                            · rcases h2bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h112, h99, hc24, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h1, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h97, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h99, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h0, hlam, p114_1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h103, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h105, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h107, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hc23, hlam, hphi, p114_1, u2ehi0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hc23, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hc23, hlam, hphi, p114_1, u2ehi3]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h0, h99, hc23, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h0, hc24, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hc24, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h110, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h0, h110, h99, hc23, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h0, hc25, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hc25, hlam, hphi, p114_1, u2ehi1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h111, hlam, p114_0]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [h112, hlam, p114_1]
                              · have p114_0 := h114c.1
                                have p114_1 := h114c.2.1
                                have p114_2 := h114c.2.2.1
                                have p114_3 := h114c.2.2.2
                                linarith only [hlam, p114_0]
                            · rcases h2bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, hc23, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h1, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h97, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h99, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, hlam, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h103, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h105, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h107, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc23, hlam, hphi, p140_1, u2ehi0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc23, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h102, h113, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p140_1, u3ehi3]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc23, hlam, hphi, p140_1, u2ehi4]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, hc24, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc24, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h110, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, h110, h99, hc23, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h0, hc25, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hc25, hlam, hphi, p140_1, u2ehi1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h111, hlam, p140_0]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [h112, hlam, p140_1]
                              · have p140_0 := h140c.1
                                have p140_1 := h140c.2.1
                                have p140_2 := h140c.2.2.1
                                have p140_3 := h140c.2.2.2
                                linarith only [hlam, p140_0]
                          · linarith only [h1, h101, h102, h112, hc23, hlam, hphi, u2ehi3]
                        · linarith only [h0, h1, h111, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h1, h110, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h1, h101, h102, h105, h109, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
              · linarith only [h0, h1, h170, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                · linarith only [h0, h172, h97, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                  · linarith only [h0, h1, h174, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                    · linarith only [h102, h172, h176, h97, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                          · linarith only [h0, h102, h178, h180, h97, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h180, h97, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h1, h179, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h1, h101, h178, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
            · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
              · linarith only [h0, h1, h186, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                · linarith only [h0, h188, h97, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                  · linarith only [h0, h190, h99, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                      · linarith only [h0, h1, h101, h193, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h1, h193, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h185, h188, h192, h97, hc24, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h197 | h197
              · linarith only [h0, h1, h197, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                · linarith only [h0, h1, h199, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                  · linarith only [h0, h1, h101, h185, h201, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                    · linarith only [h1, h101, h185, h199, h203, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                      · linarith only [h0, h1, h101, h205, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h1, h205, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h208 | h208
    · rcases m.htr 0 2 4 (by decide) (by decide) with h209 | h209
      · rcases m.htr 0 2 5 (by decide) (by decide) with h210 | h210
        · rcases m.htr 0 3 4 (by decide) (by decide) with h211 | h211
          · rcases m.htr 0 4 5 (by decide) (by decide) with h212 | h212
            · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
              · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h218 | h218
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                            · linarith only [h208, h217, h220, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h209, h219, h220, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h223 | h223
                            · linarith only [h219, h223, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h2bigk with h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c | h225c
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h0, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h0, h218, hc12, hlam, hphi, ht01, ht0b, ht5b, p225_1, u5ehi3]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                rcases p225_3 (m.d 0 2) (by simp) with h229 | h229
                                · rcases p225_3 (m.d 1 2) (by simp) with h230 | h230
                                  · rcases p225_3 (m.d 2 3) (by simp) with h231 | h231
                                    · linarith only [h208, h231, hlam]
                                    · linarith only [h217, h231, hlam]
                                  · linarith only [h214, h230, hlam]
                                · linarith only [h229, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                rcases p225_3 (m.d 0 2) (by simp) with h236 | h236
                                · rcases p225_3 (m.d 1 2) (by simp) with h237 | h237
                                  · rcases p225_3 (m.d 2 3) (by simp) with h238 | h238
                                    · linarith only [h208, h238, hlam]
                                    · linarith only [h218, h238, hlam]
                                  · linarith only [h215, h237, hlam]
                                · linarith only [h236, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h208, h211, h212, h219, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p225_1, u2ehi3]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h218, h223, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p225_1, u3ehi3]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                rcases p225_3 (m.d 0 2) (by simp) with h246 | h246
                                · linarith only [h0, h246, hlam]
                                · linarith only [h209, h246, hlam]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                rcases p225_3 (m.d 0 2) (by simp) with h249 | h249
                                · linarith only [h0, h249, hlam]
                                · linarith only [h210, h249, hlam]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h208, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h213, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hc23, hlam, hphi, p225_1, u2ehi3]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h208, hc02, hlam, hphi, ht0b, ht5b, p225_1, u5ehi2]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h209, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h214, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h217, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h219, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h210, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h215, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [h218, hlam, p225_0]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hc25, hlam, hphi, p225_1, u2ehi3]
                              · have p225_0 := h225c.1
                                have p225_1 := h225c.2.1
                                have p225_2 := h225c.2.2.1
                                have p225_3 := h225c.2.2.2
                                linarith only [hlam, p225_0]
                        · linarith only [h217, h218, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                        · linarith only [h217, h268, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h271 | h271
                            · rcases h2bigk with h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c | h272c
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h0, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                rcases p272_3 (m.d 0 2) (by simp) with h275 | h275
                                · rcases p272_3 (m.d 1 2) (by simp) with h276 | h276
                                  · rcases p272_3 (m.d 2 3) (by simp) with h277 | h277
                                    · linarith only [h277, hlam, p272_0]
                                    · rcases p272_3 (m.d 2 4) (by simp) with h279 | h279
                                      · linarith only [h209, h279, hlam]
                                      · linarith only [h217, h279, hlam]
                                  · linarith only [h213, h276, hlam]
                                · linarith only [h275, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h0, h270, hc12, hlam, hphi, ht01, ht0b, ht5b, p272_1, u5ehi4]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                rcases p272_3 (m.d 0 2) (by simp) with h285 | h285
                                · rcases p272_3 (m.d 1 2) (by simp) with h286 | h286
                                  · rcases p272_3 (m.d 2 3) (by simp) with h287 | h287
                                    · linarith only [h208, h287, hlam]
                                    · rcases p272_3 (m.d 2 4) (by simp) with h289 | h289
                                      · linarith only [h209, h289, hlam]
                                      · linarith only [h270, h289, hlam]
                                  · linarith only [h215, h286, hlam]
                                · linarith only [h285, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h208, h211, h268, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p272_1, u2ehi2]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                rcases p272_3 (m.d 0 2) (by simp) with h296 | h296
                                · linarith only [h0, h296, hlam]
                                · linarith only [h208, h296, hlam]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h270, hc12, hlam, hphi, ht01, ht0b, ht5b, p272_1, u5ehi4]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                rcases p272_3 (m.d 0 2) (by simp) with h300 | h300
                                · linarith only [h0, h300, hlam]
                                · linarith only [h210, h300, hlam]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h208, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h213, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h217, hlam, p272_1]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h268, hlam, p272_1]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h209, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h214, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hc24, hlam, hphi, p272_1, u2ehi2]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h208, h211, h217, hc02, hlam, hphi, ht0b, ht5b, p272_1, u5ehi2]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h210, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h215, hlam, p272_0]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hc25, hlam, hphi, p272_1, u2ehi2]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [h270, hlam, p272_1]
                              · have p272_0 := h272c.1
                                have p272_1 := h272c.2.1
                                have p272_2 := h272c.2.2.1
                                have p272_3 := h272c.2.2.2
                                linarith only [hlam, p272_0]
                            · linarith only [h0, h208, h211, h212, h217, h271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                            · linarith only [h0, h208, h211, h217, h270, h319, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h216, h217, h319, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                          · linarith only [h214, h216, h324, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                            · linarith only [h213, h214, h216, h322, h326, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases h2bigk with h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h0, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h0, h322, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p328_1, u3ehi3]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                rcases p328_3 (m.d 0 2) (by simp) with h332 | h332
                                · rcases p328_3 (m.d 1 2) (by simp) with h333 | h333
                                  · rcases p328_3 (m.d 2 3) (by simp) with h334 | h334
                                    · linarith only [h208, h334, hlam]
                                    · linarith only [h322, h334, hlam]
                                  · linarith only [h214, h333, hlam]
                                · linarith only [h332, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                rcases p328_3 (m.d 0 2) (by simp) with h339 | h339
                                · rcases p328_3 (m.d 1 2) (by simp) with h340 | h340
                                  · rcases p328_3 (m.d 2 3) (by simp) with h341 | h341
                                    · linarith only [h208, h341, hlam]
                                    · linarith only [h323, h341, hlam]
                                  · linarith only [h215, h340, hlam]
                                · linarith only [h339, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h208, h323, h326, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p328_1, u3ehi3]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h323, h326, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p328_1, u3ehi3]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                rcases p328_3 (m.d 0 2) (by simp) with h349 | h349
                                · linarith only [h0, h349, hlam]
                                · linarith only [h209, h349, hlam]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                rcases p328_3 (m.d 0 2) (by simp) with h352 | h352
                                · linarith only [h0, h352, hlam]
                                · linarith only [h210, h352, hlam]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h208, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h213, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hc23, hlam, hphi, p328_1, u2ehi3]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h0, h208, hc12, hlam, hphi, ht01, ht0b, ht5b, p328_1, u5ehi2]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h209, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h214, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h322, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h324, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h210, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h215, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [h323, hlam, p328_0]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hc25, hlam, hphi, p328_1, u2ehi3]
                              · have p328_0 := h328c.1
                                have p328_1 := h328c.2.1
                                have p328_2 := h328c.2.2.1
                                have p328_3 := h328c.2.2.2
                                linarith only [hlam, p328_0]
                        · linarith only [h322, h323, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h371 | h371
                        · linarith only [h212, h214, h216, h322, h371, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h373 | h373
                          · linarith only [h214, h216, h373, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h375 | h375
                            · linarith only [h0, h208, h211, h214, h216, h322, h375, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h322, h375, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h210, h215, hlam]
                · linarith only [h0, h210, h214, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h209, h213, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h381 | h381
              · rcases m.htr 1 2 4 (by decide) (by decide) with h382 | h382
                · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h384 | h384
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h386 | h386
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
                          · linarith only [h209, h212, h387, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h389 | h389
                            · linarith only [h208, h209, h212, h385, h389, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases h2bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h386, hc12, hlam, hphi, ht01, ht0b, ht5b, p391_1, u5ehi3]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                rcases p391_3 (m.d 0 2) (by simp) with h395 | h395
                                · rcases p391_3 (m.d 1 2) (by simp) with h396 | h396
                                  · rcases p391_3 (m.d 2 3) (by simp) with h397 | h397
                                    · linarith only [h208, h397, hlam]
                                    · linarith only [h385, h397, hlam]
                                  · linarith only [h382, h396, hlam]
                                · linarith only [h395, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                rcases p391_3 (m.d 0 2) (by simp) with h402 | h402
                                · rcases p391_3 (m.d 1 2) (by simp) with h403 | h403
                                  · rcases p391_3 (m.d 2 3) (by simp) with h404 | h404
                                    · linarith only [h208, h404, hlam]
                                    · linarith only [h386, h404, hlam]
                                  · linarith only [h383, h403, hlam]
                                · linarith only [h402, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h208, h386, h389, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p391_1, u3ehi3]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h386, h389, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p391_1, u3ehi3]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                rcases p391_3 (m.d 0 2) (by simp) with h412 | h412
                                · linarith only [h0, h412, hlam]
                                · linarith only [h209, h412, hlam]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                rcases p391_3 (m.d 0 2) (by simp) with h415 | h415
                                · linarith only [h0, h415, hlam]
                                · linarith only [h210, h415, hlam]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h208, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h381, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h208, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p391_1, u2ehi3]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h0, h208, h386, h389, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p391_1, u3ehi3]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h209, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h382, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h385, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h387, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h210, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h383, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [h386, hlam, p391_0]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hc25, hlam, hphi, p391_1, u2ehi3]
                              · have p391_0 := h391c.1
                                have p391_1 := h391c.2.1
                                have p391_2 := h391c.2.2.1
                                have p391_3 := h391c.2.2.2
                                linarith only [hlam, p391_0]
                        · linarith only [h385, h386, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h211, h212, h382, h384, h385, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h437 | h437
                          · linarith only [h209, h212, h437, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                            · linarith only [h209, h212, h439, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h2bigk with h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c | h441c
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h436, h439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p441_1, u3ehi3]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                rcases p441_3 (m.d 0 2) (by simp) with h445 | h445
                                · rcases p441_3 (m.d 1 2) (by simp) with h446 | h446
                                  · rcases p441_3 (m.d 2 3) (by simp) with h447 | h447
                                    · linarith only [h208, h447, hlam]
                                    · linarith only [h435, h447, hlam]
                                  · linarith only [h382, h446, hlam]
                                · linarith only [h445, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                rcases p441_3 (m.d 0 2) (by simp) with h452 | h452
                                · rcases p441_3 (m.d 1 2) (by simp) with h453 | h453
                                  · rcases p441_3 (m.d 2 3) (by simp) with h454 | h454
                                    · linarith only [h208, h454, hlam]
                                    · linarith only [h436, h454, hlam]
                                  · linarith only [h383, h453, hlam]
                                · linarith only [h452, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h208, h436, h439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p441_1, u3ehi3]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h436, h439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p441_1, u3ehi3]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                rcases p441_3 (m.d 0 2) (by simp) with h462 | h462
                                · linarith only [h0, h462, hlam]
                                · linarith only [h209, h462, hlam]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                rcases p441_3 (m.d 0 2) (by simp) with h465 | h465
                                · linarith only [h0, h465, hlam]
                                · linarith only [h210, h465, hlam]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h208, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h381, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h208, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p441_1, u2ehi3]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h0, h208, hc12, hlam, hphi, ht01, ht0b, ht5b, p441_1, u5ehi2]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h209, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h382, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h435, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h437, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h210, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h383, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [h436, hlam, p441_0]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hc25, hlam, hphi, p441_1, u2ehi3]
                              · have p441_0 := h441c.1
                                have p441_1 := h441c.2.1
                                have p441_2 := h441c.2.2.1
                                have p441_3 := h441c.2.2.2
                                linarith only [hlam, p441_0]
                        · linarith only [h435, h436, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h211, h212, h435, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h0, h210, h383, hlam]
                · linarith only [h0, h210, h382, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h210, h381, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
            · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
              · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                · rcases m.htr 1 2 5 (by decide) (by decide) with h491 | h491
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                      · linarith only [h208, h211, h493, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h495 | h495
                        · linarith only [h208, h211, h495, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h497 | h497
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h498 | h498
                            · rcases h2bigk with h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h0, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                rcases p499_3 (m.d 0 2) (by simp) with h502 | h502
                                · rcases p499_3 (m.d 1 2) (by simp) with h503 | h503
                                  · rcases p499_3 (m.d 2 3) (by simp) with h504 | h504
                                    · linarith only [h504, hlam, p499_0]
                                    · rcases p499_3 (m.d 2 4) (by simp) with h506 | h506
                                      · linarith only [h209, h506, hlam]
                                      · linarith only [h493, h506, hlam]
                                  · linarith only [h489, h503, hlam]
                                · linarith only [h502, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h0, h497, hc12, hlam, hphi, ht01, ht0b, ht5b, p499_1, u5ehi4]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                rcases p499_3 (m.d 0 2) (by simp) with h512 | h512
                                · rcases p499_3 (m.d 1 2) (by simp) with h513 | h513
                                  · rcases p499_3 (m.d 2 3) (by simp) with h514 | h514
                                    · linarith only [h208, h514, hlam]
                                    · rcases p499_3 (m.d 2 4) (by simp) with h516 | h516
                                      · linarith only [h209, h516, hlam]
                                      · linarith only [h497, h516, hlam]
                                  · linarith only [h491, h513, hlam]
                                · linarith only [h512, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h208, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p499_1, u2ehi2]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                rcases p499_3 (m.d 0 2) (by simp) with h523 | h523
                                · linarith only [h0, h523, hlam]
                                · linarith only [h208, h523, hlam]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h497, hc12, hlam, hphi, ht01, ht0b, ht5b, p499_1, u5ehi4]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                rcases p499_3 (m.d 0 2) (by simp) with h527 | h527
                                · linarith only [h0, h527, hlam]
                                · linarith only [h210, h527, hlam]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h208, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h489, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h493, hlam, p499_1]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h495, hlam, p499_1]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h209, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h490, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h209, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p499_1, u2ehi2]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h0, h209, h495, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p499_1, u2ehi2]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h210, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h491, hlam, p499_0]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [hc25, hlam, hphi, p499_1, u2ehi2]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [h497, hlam, p499_1]
                              · have p499_0 := h499c.1
                                have p499_1 := h499c.2.1
                                have p499_2 := h499c.2.2.1
                                have p499_3 := h499c.2.2.2
                                linarith only [hlam, p499_0]
                            · linarith only [h208, h211, h498, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h211, h488, h497, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h211, h488, h490, h492, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h210, h491, hlam]
                · linarith only [h0, h210, h490, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h210, h489, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h551 | h551
              · rcases m.htr 1 2 4 (by decide) (by decide) with h552 | h552
                · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h555 | h555
                      · linarith only [h208, h211, h488, h552, h554, h555, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h557 | h557
                        · linarith only [h208, h211, h488, h552, h554, h557, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h559 | h559
                          · linarith only [h208, h209, h211, h488, h559, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h561 | h561
                            · linarith only [h208, h211, h488, h561, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h208, h211, h554, h561, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                      · linarith only [h208, h211, h564, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h566 | h566
                        · linarith only [h208, h211, h566, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h568 | h568
                          · linarith only [h209, h488, h568, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                            · linarith only [h211, h488, h570, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h208, h211, h570, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h208, h553, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h209, h552, hlam]
              · linarith only [h0, h208, h551, hlam]
        · linarith only [h208, h210, hc25, hlam, hphi, u2ehi2]
      · linarith only [h208, h209, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h578 | h578
      · linarith only [h208, h578, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h580 | h580
        · linarith only [h208, h580, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
          · rcases m.htr 0 4 5 (by decide) (by decide) with h583 | h583
            · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
              · rcases m.htr 1 2 4 (by decide) (by decide) with h585 | h585
                · rcases m.htr 1 2 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h588 | h588
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h589 | h589
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h591 | h591
                            · linarith only [h208, h582, h584, h591, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h578, h583, h584, h588, h591, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h578, h583, h590, hlam]
                        · linarith only [h208, h589, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h208, h582, h588, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h578, h583, h585, h587, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h208, h584, h586, hc25, hlam, hphi, u2ehi0]
                · linarith only [h208, h584, h585, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                · linarith only [h584, h600, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                  · linarith only [h584, h602, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h604 | h604
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h607 | h607
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h608 | h608
                            · rcases h2bigk with h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h0, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h208, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h578, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h580, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h602, h605, h607, hc23, hlam, hphi, p609_1, u2ehi0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h584, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h600, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h602, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hc23, hlam, hphi, p609_1, u2ehi0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hc23, hlam, hphi, p609_1, u2ehi1]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hc23, hlam, hphi, p609_1, u2ehi3]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h0, h602, hc01, hc23, hlam, hphi, ht12, p609_1]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hc24, hlam, hphi, p609_1, u2ehi0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p609_1]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h605, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h0, h602, h605, hc01, hc23, hlam, hphi, ht12, p609_1]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hc25, hlam, hphi, p609_1, u2ehi0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p609_1]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h606, hlam, p609_0]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [h607, hlam, p609_1]
                              · have p609_0 := h609c.1
                                have p609_1 := h609c.2.1
                                have p609_2 := h609c.2.2.1
                                have p609_3 := h609c.2.2.2
                                linarith only [hlam, p609_0]
                            · rcases h2bigk with h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h0, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h208, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h578, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h580, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h584, hc23, hlam, hphi, p635_1, u2ehi0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h584, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h600, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h602, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hc23, hlam, hphi, p635_1, u2ehi0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hc23, hlam, hphi, p635_1, u2ehi1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hc23, hlam, hphi, p635_1, u2ehi3]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h0, h602, hc01, hc23, hlam, hphi, ht12, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hc24, hlam, hphi, p635_1, u2ehi0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h605, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h0, h602, h605, hc01, hc23, hlam, hphi, ht12, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hc25, hlam, hphi, p635_1, u2ehi0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h606, hlam, p635_0]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [h607, hlam, p635_1]
                              · have p635_0 := h635c.1
                                have p635_1 := h635c.2.1
                                have p635_2 := h635c.2.2.1
                                have p635_3 := h635c.2.2.2
                                linarith only [hlam, p635_0]
                          · linarith only [h208, h582, h583, h607, hc23, hlam, hphi, u2ehi3]
                        · linarith only [h208, h606, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h582, h584, h605, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h208, h582, h583, h600, h604, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
              · rcases m.htr 1 2 4 (by decide) (by decide) with h666 | h666
                · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h669 | h669
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h670 | h670
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h671 | h671
                          · linarith only [h578, h583, h671, hc24, hlam, hphi, u2ehi0]
                          · linarith only [h578, h666, h668, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h208, h670, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h208, h582, h669, hlam]
                    · linarith only [h578, h666, h668, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h208, h665, h667, hc25, hlam, hphi, u2ehi0]
                · linarith only [h208, h665, h666, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                · linarith only [h665, h679, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
                  · linarith only [h665, h681, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h683 | h683
                    · linarith only [h578, h583, h679, h683, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h686 | h686
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h687 | h687
                          · linarith only [h679, h683, h685, h687, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h578, h687, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h208, h686, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h665, h685, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h692 | h692
            · rcases m.htr 1 2 3 (by decide) (by decide) with h693 | h693
              · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
                · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h696 | h696
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h697 | h697
                      · linarith only [h582, h693, h697, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h208, h697, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h578, h692, h694, h696, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h578, h692, h694, h695, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h208, h693, h694, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h703 | h703
                · linarith only [h693, h703, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h705 | h705
                  · linarith only [h693, h705, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h707 | h707
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h708 | h708
                      · linarith only [h208, h582, h708, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h693, h708, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h0, h578, h692, h703, h707, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
              · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                · rcases m.htr 1 2 5 (by decide) (by decide) with h714 | h714
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h715 | h715
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h716 | h716
                      · linarith only [h208, h582, h716, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h208, h716, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h578, h713, h715, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h208, h712, h714, hc25, hlam, hphi, u2ehi0]
                · linarith only [h208, h712, h713, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
                · linarith only [h712, h722, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                  · linarith only [h712, h724, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h726 | h726
                    · linarith only [h208, h582, h692, h722, h726, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h728 | h728
                      · linarith only [h208, h582, h728, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h208, h728, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
