import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_R_L_R_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h10, h11, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h0, h11, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h10, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h16, h9, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h15, h18, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · rcases h4bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              rcases p20_3 (m.d 0 4) (by simp) with h22 | h22
                              · rcases p20_3 (m.d 1 4) (by simp) with h23 | h23
                                · linarith only [h2, h23, hlam]
                                · rcases p20_3 (m.d 2 4) (by simp) with h25 | h25
                                  · linarith only [h25, h3, hlam]
                                  · rcases p20_3 (m.d 3 4) (by simp) with h27 | h27
                                    · linarith only [h27, h4, hlam]
                                    · rcases p20_3 (m.d 4 5) (by simp) with h29 | h29
                                      · linarith only [h29, h5, hlam]
                                      · linarith only [h29, h9, hlam]
                              · linarith only [h2, h22, hlam]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              rcases p20_3 (m.d 0 4) (by simp) with h33 | h33
                              · rcases p20_3 (m.d 1 4) (by simp) with h34 | h34
                                · linarith only [h2, h34, hlam]
                                · linarith only [h34, h7, hlam]
                              · linarith only [h3, h33, hlam]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              rcases p20_3 (m.d 0 4) (by simp) with h38 | h38
                              · rcases p20_3 (m.d 1 4) (by simp) with h39 | h39
                                · linarith only [h2, h39, hlam]
                                · linarith only [h39, h8, hlam]
                              · linarith only [h38, h4, hlam]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h0, h3, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p20_1, u1ehi3]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h2, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h9, hc24, hc45, hlam, hphi, p20_1]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h0, h3, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h9, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h3, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h7, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h0, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p20_1]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h16, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h4, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h8, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h15, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h18, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h5, hlam, p20_0]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p20_1, u1ehi3]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p20_1, u2ehi3]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              rcases p20_3 (m.d 0 4) (by simp) with h62 | h62
                              · rcases p20_3 (m.d 1 4) (by simp) with h63 | h63
                                · linarith only [h63, h9, hlam]
                                · linarith only [h63, h8, hlam]
                              · linarith only [h4, h62, hlam]
                            · have p20_0 := h20c.1
                              have p20_1 := h20c.2.1
                              have p20_2 := h20c.2.2.1
                              have p20_3 := h20c.2.2.2
                              linarith only [hlam, p20_0]
                      · linarith only [h0, h15, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                      · linarith only [h70, h8, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                        · linarith only [h0, h7, h72, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h2, h69, h72, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                      · linarith only [h6, h75, h8, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                        · linarith only [h69, h77, h8, hc24, hlam, hphi, ht12, u1ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                          · linarith only [h1, h4, h69, h79, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                          · linarith only [h79, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h0, h3, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                · linarith only [h6, h83, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                          · linarith only [h1, h85, h89, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h4bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h0, h3, h86, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h0, h3, h83, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1, u2ehi1]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              rcases p91_3 (m.d 0 4) (by simp) with h95 | h95
                              · rcases p91_3 (m.d 1 4) (by simp) with h96 | h96
                                · linarith only [h2, h96, hlam]
                                · linarith only [h85, h96, hlam]
                              · linarith only [h4, h95, hlam]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              rcases p91_3 (m.d 0 4) (by simp) with h100 | h100
                              · rcases p91_3 (m.d 1 4) (by simp) with h101 | h101
                                · linarith only [h101, h2, hlam]
                                · linarith only [h101, h86, hlam]
                              · linarith only [h100, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h2, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h83, hlam, p91_1]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              rcases p91_3 (m.d 0 4) (by simp) with h108 | h108
                              · rcases p91_3 (m.d 1 4) (by simp) with h109 | h109
                                · rcases p91_3 (m.d 2 4) (by simp) with h110 | h110
                                  · rcases p91_3 (m.d 3 4) (by simp) with h111 | h111
                                    · linarith only [h111, h85, hlam]
                                    · rcases p91_3 (m.d 4 5) (by simp) with h113 | h113
                                      · linarith only [h113, h86, hlam]
                                      · linarith only [h113, h89, hlam]
                                  · linarith only [h110, h87, hlam]
                                · linarith only [h109, h85, hlam]
                              · linarith only [h108, h4, hlam]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h2, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h3, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [hc24, hlam, hphi, ht12, p91_1, u1ehi3]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              rcases p91_3 (m.d 0 4) (by simp) with h123 | h123
                              · rcases p91_3 (m.d 1 4) (by simp) with h124 | h124
                                · linarith only [h124, h83, hlam]
                                · linarith only [h124, h85, hlam]
                              · linarith only [h123, h4, hlam]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h0, h3, h89, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h4, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h85, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h87, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h89, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h5, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h86, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h88, hlam, p91_0]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [h1, h85, h86, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p91_1]
                            · have p91_0 := h91c.1
                              have p91_1 := h91c.2.1
                              have p91_2 := h91c.2.2.1
                              have p91_3 := h91c.2.2.2
                              linarith only [hlam, p91_0]
                        · linarith only [h83, h86, h88, hlam]
                      · linarith only [h6, h87, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                        · linarith only [h0, h142, h3, h83, h86, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · linarith only [h0, h142, h3, h5, h83, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                      · linarith only [h141, h6, h85, hc14, hlam, hphi, u1ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                      · linarith only [h147, h6, h85, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h147, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                      · linarith only [h150, h6, h85, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h150, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
              · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
                · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                    · linarith only [h156, h2, h5, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                        · linarith only [h153, h158, h159, h2, h5, hc12, hlam, hphi, u1ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                          · linarith only [h0, h153, h158, h161, h2, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · rcases h4bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h5, hc45, hlam, hphi, ht12, ht23, ht34, p163_1, u1ehi3]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h5, hc24, hc45, hlam, hphi, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h5, hc34, hc45, hlam, hphi, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h5, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h2, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi3]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h2, h5, hc34, hc45, hlam, hphi, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h156, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h3, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h154, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h3, h5, hc34, hc45, hlam, hphi, p163_1]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h159, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h4, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h155, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h158, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h161, hlam, p163_0]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p163_1, u1ehi3]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p163_1, u1ehi3]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p163_1, u2ehi3]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              rcases p163_3 (m.d 0 4) (by simp) with h187 | h187
                              · linarith only [h187, h5, hlam]
                              · linarith only [h187, h4, hlam]
                            · have p163_0 := h163c.1
                              have p163_1 := h163c.2.1
                              have p163_2 := h163c.2.2.1
                              have p163_3 := h163c.2.2.2
                              linarith only [hlam, p163_0]
                      · linarith only [h158, h4, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h155, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h154, h3, h5, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                · linarith only [h153, h194, hc23, hlam, hphi, u2ehi3]
                · linarith only [h194, h3, h5, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
            · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
              · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                · rcases m.htr 1 3 4 (by decide) (by decide) with h200 | h200
                  · linarith only [h1, h200, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                      · linarith only [h1, h198, h203, h4, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h205 | h205
                        · linarith only [h0, h199, h205, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h2, h202, h205, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h197, h202, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h0, h198, h199, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                · linarith only [h198, h210, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h212 | h212
                  · linarith only [h1, h212, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                      · linarith only [h1, h215, h4, hc23, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h198, h215, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h197, h214, h4, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
              · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
                · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h1, h221, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                    · linarith only [h197, h2, h223, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                      · linarith only [h1, h219, h225, h4, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h1, h197, h220, h227, h4, hc14, hlam, hphi, u1ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                          · linarith only [h197, h2, h229, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h1, h229, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h197, h220, h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                · linarith only [h219, h233, hc23, hlam, hphi, u2ehi3]
                · linarith only [h197, h233, h3, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h236 | h236
          · rcases m.htr 0 4 5 (by decide) (by decide) with h237 | h237
            · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
              · linarith only [h0, h238, h3, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                · linarith only [h0, h240, h3, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h242 | h242
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h246 | h246
                          · linarith only [h1, h242, h246, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h4bigk with h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h240, h244, h3, hc23, hlam, hphi, ht12, p248_1, u1ehi1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h3, hlam, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              rcases p248_3 (m.d 0 4) (by simp) with h252 | h252
                              · rcases p248_3 (m.d 1 4) (by simp) with h253 | h253
                                · linarith only [h2, h253, hlam]
                                · linarith only [h242, h253, hlam]
                              · linarith only [h236, h252, hlam]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              rcases p248_3 (m.d 0 4) (by simp) with h257 | h257
                              · rcases p248_3 (m.d 1 4) (by simp) with h258 | h258
                                · linarith only [h2, h258, hlam]
                                · linarith only [h243, h258, hlam]
                              · linarith only [h257, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h2, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h240, hlam, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              rcases p248_3 (m.d 0 4) (by simp) with h265 | h265
                              · rcases p248_3 (m.d 1 4) (by simp) with h266 | h266
                                · rcases p248_3 (m.d 2 4) (by simp) with h267 | h267
                                  · rcases p248_3 (m.d 3 4) (by simp) with h268 | h268
                                    · linarith only [h242, h268, hlam]
                                    · rcases p248_3 (m.d 4 5) (by simp) with h270 | h270
                                      · linarith only [h243, h270, hlam]
                                      · linarith only [h246, h270, hlam]
                                  · linarith only [h244, h267, hlam]
                                · linarith only [h242, h266, hlam]
                              · linarith only [h236, h265, hlam]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h2, h246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h2, h244, hc23, hlam, hphi, ht12, p248_1, u1ehi3]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h244, hc23, hlam, hphi, ht12, p248_1, u1ehi3]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              rcases p248_3 (m.d 0 4) (by simp) with h280 | h280
                              · linarith only [h280, h3, hlam]
                              · linarith only [h236, h280, hlam]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              rcases p248_3 (m.d 0 4) (by simp) with h283 | h283
                              · linarith only [h283, h3, hlam]
                              · linarith only [h237, h283, hlam]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h236, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h242, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h244, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h246, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h237, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h243, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h245, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h2, h243, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                        · linarith only [h1, h242, h243, h245, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h236, h238, h242, h243, h244, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h237, h243, h3, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                      · linarith only [h238, h242, h300, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h1, h236, h238, h300, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · linarith only [h237, h299, h3, hc24, hlam, hphi, ht12, u1ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
              · linarith only [h0, h3, h304, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                · linarith only [h0, h237, h3, h306, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                    · linarith only [h0, h237, h3, h308, h309, hc13, hlam, hphi, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                        · linarith only [h0, h237, h3, h311, h312, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h3, h312, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                      · linarith only [h1, h308, h311, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h236, h237, h308, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h317 | h317
            · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
              · linarith only [h0, h3, h318, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h320 | h320
                · linarith only [h1, h236, h3, h318, h320, hc34, hlam, hphi, ht23, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
                  · linarith only [h1, h236, h322, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                      · linarith only [h1, h236, h318, h325, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h318, h325, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h236, h317, h324, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h329 | h329
              · linarith only [h0, h3, h329, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                · linarith only [h329, h331, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                  · linarith only [h1, h236, h333, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                    · linarith only [h1, h236, h317, h329, h335, hc14, hlam, hphi, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                      · linarith only [h1, h236, h329, h337, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h329, h337, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h342 | h342
    · linarith only [h0, h342, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h344 | h344
      · linarith only [h0, h344, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h346 | h346
        · rcases m.htr 0 3 4 (by decide) (by decide) with h347 | h347
          · rcases m.htr 0 4 5 (by decide) (by decide) with h348 | h348
            · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
              · rcases m.htr 1 2 4 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h355 | h355
                          · linarith only [h349, h353, h355, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases h4bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h344, hlam, p357_1]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h347, h354, h355, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p357_1]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              rcases p357_3 (m.d 0 4) (by simp) with h361 | h361
                              · rcases p357_3 (m.d 1 4) (by simp) with h362 | h362
                                · rcases p357_3 (m.d 2 4) (by simp) with h363 | h363
                                  · linarith only [h346, h363, hlam]
                                  · linarith only [h353, h363, hlam]
                                · linarith only [h351, h362, hlam]
                              · linarith only [h347, h361, hlam]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              rcases p357_3 (m.d 0 4) (by simp) with h368 | h368
                              · rcases p357_3 (m.d 1 4) (by simp) with h369 | h369
                                · rcases p357_3 (m.d 2 4) (by simp) with h370 | h370
                                  · linarith only [h346, h370, hlam]
                                  · linarith only [h354, h370, hlam]
                                · linarith only [h352, h369, hlam]
                              · linarith only [h368, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h344, h349, h351, hc12, hlam, hphi, p357_1, u1ehi0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h349, h351, h354, h355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p357_1]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              rcases p357_3 (m.d 0 4) (by simp) with h378 | h378
                              · linarith only [h344, h378, hlam]
                              · linarith only [h347, h378, hlam]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              rcases p357_3 (m.d 0 4) (by simp) with h381 | h381
                              · linarith only [h344, h381, hlam]
                              · linarith only [h348, h381, hlam]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h346, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h350, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              rcases p357_3 (m.d 0 4) (by simp) with h387 | h387
                              · rcases p357_3 (m.d 1 4) (by simp) with h388 | h388
                                · rcases p357_3 (m.d 2 4) (by simp) with h389 | h389
                                  · rcases p357_3 (m.d 3 4) (by simp) with h390 | h390
                                    · linarith only [h353, h390, hlam]
                                    · rcases p357_3 (m.d 4 5) (by simp) with h392 | h392
                                      · linarith only [h354, h392, hlam]
                                      · linarith only [h355, h392, hlam]
                                  · linarith only [h353, h389, hlam]
                                · linarith only [h351, h388, hlam]
                              · linarith only [h347, h387, hlam]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h346, h355, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p357_1]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h347, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h351, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h353, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h355, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h348, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h352, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h354, hlam, p357_0]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [h0, h346, h354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p357_1]
                            · have p357_0 := h357c.1
                              have p357_1 := h357c.2.1
                              have p357_2 := h357c.2.2.1
                              have p357_3 := h357c.2.2.2
                              linarith only [hlam, p357_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                          · linarith only [h354, h409, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h4bigk with h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h344, hlam, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h414 | h414
                              · rcases p411_3 (m.d 1 4) (by simp) with h415 | h415
                                · rcases p411_3 (m.d 2 4) (by simp) with h416 | h416
                                  · linarith only [h346, h416, hlam]
                                  · rcases p411_3 (m.d 3 4) (by simp) with h418 | h418
                                    · linarith only [h347, h418, hlam]
                                    · rcases p411_3 (m.d 4 5) (by simp) with h420 | h420
                                      · linarith only [h348, h420, hlam]
                                      · linarith only [h354, h420, hlam]
                                · linarith only [h350, h415, hlam]
                              · linarith only [h346, h414, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h425 | h425
                              · rcases p411_3 (m.d 1 4) (by simp) with h426 | h426
                                · rcases p411_3 (m.d 2 4) (by simp) with h427 | h427
                                  · linarith only [h346, h427, hlam]
                                  · linarith only [h353, h427, hlam]
                                · linarith only [h351, h426, hlam]
                              · linarith only [h347, h425, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h354, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p411_1, u2ehi3]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h344, h349, h351, hc12, hlam, hphi, p411_1, u1ehi0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h435 | h435
                              · linarith only [h344, h435, hlam]
                              · linarith only [h346, h435, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h438 | h438
                              · linarith only [h344, h438, hlam]
                              · linarith only [h347, h438, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h349, h351, h354, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p411_1, u2ehi3]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h346, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h350, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h348, h354, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p411_1]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h354, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h347, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h351, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h353, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h409, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h348, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h352, hlam, p411_0]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [h348, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p411_1, u2ehi3]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              rcases p411_3 (m.d 0 4) (by simp) with h455 | h455
                              · rcases p411_3 (m.d 1 4) (by simp) with h456 | h456
                                · rcases p411_3 (m.d 2 4) (by simp) with h457 | h457
                                  · linarith only [h354, h457, hlam]
                                  · linarith only [h353, h457, hlam]
                                · linarith only [h351, h456, hlam]
                              · linarith only [h347, h455, hlam]
                            · have p411_0 := h411c.1
                              have p411_1 := h411c.2.1
                              have p411_2 := h411c.2.2.1
                              have p411_3 := h411c.2.2.2
                              linarith only [hlam, p411_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h463 | h463
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h464 | h464
                          · rcases h4bigk with h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h344, hlam, p465_1]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h344, h349, h351, h463, hc12, hlam, hphi, ht01, ht0b, ht5b, p465_1, u5ehi4]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h344, h349, h351, h353, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p465_1, u2ehi2]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              rcases p465_3 (m.d 0 4) (by simp) with h470 | h470
                              · rcases p465_3 (m.d 1 4) (by simp) with h471 | h471
                                · rcases p465_3 (m.d 2 4) (by simp) with h472 | h472
                                  · linarith only [h346, h472, hlam]
                                  · linarith only [h463, h472, hlam]
                                · linarith only [h352, h471, hlam]
                              · linarith only [h470, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h344, h349, h351, hc12, hlam, hphi, p465_1, u1ehi0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h349, h351, h463, hc12, hlam, hphi, ht01, ht0b, ht5b, p465_1, u5ehi4]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h349, h351, h353, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p465_1, u2ehi2]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              rcases p465_3 (m.d 0 4) (by simp) with h481 | h481
                              · linarith only [h344, h481, hlam]
                              · linarith only [h348, h481, hlam]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h346, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h350, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h353, hlam, p465_1]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h0, h346, hc12, hlam, hphi, ht01, ht0b, ht5b, p465_1, u5ehi4]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h347, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h351, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [hc34, hlam, hphi, ht23, p465_1, u2ehi3]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h342, h347, h349, hc12, hlam, hphi, ht01, ht0b, ht5b, p465_1, u5ehi4]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h348, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h352, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h463, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [h464, hlam, p465_0]
                            · have p465_0 := h465c.1
                              have p465_1 := h465c.2.1
                              have p465_2 := h465c.2.2.1
                              have p465_3 := h465c.2.2.2
                              linarith only [hlam, p465_0]
                          · linarith only [h353, h463, h464, hc24, hlam, hphi, u2ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h500 | h500
                          · linarith only [h342, h347, h349, h353, h463, h500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h348, h353, h500, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h342, h347, h348, h349, h352, hc12, hlam, hphi, u1ehi3]
                  · linarith only [h342, h351, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h350, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h349, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
              · rcases m.htr 1 2 4 (by decide) (by decide) with h508 | h508
                · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h510 | h510
                    · linarith only [h344, h348, h507, h509, h510, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h344, h510, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                  · linarith only [h342, h347, h509, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                · linarith only [h346, h507, h508, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h507, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h516 | h516
            · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
              · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
                · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
                  · linarith only [h342, h347, h519, hc13, hlam, hphi, u1ehi0]
                  · linarith only [h342, h519, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h346, h518, hlam]
              · linarith only [h0, h346, h517, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
              · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                  · linarith only [h342, h347, h524, h526, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h342, h526, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h346, h524, h525, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h524, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h531 | h531
          · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
            · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
              · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                · linarith only [h0, h346, h534, hc12, hlam, hphi, u1ehi0]
                · linarith only [h533, h534, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h533, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
              · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                · linarith only [h0, h346, h539, hc12, hlam, hphi, u1ehi0]
                · linarith only [h538, h539, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h538, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h543 | h543
            · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
              · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                · linarith only [h0, h346, h545, hc12, hlam, hphi, u1ehi0]
                · linarith only [h544, h545, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h544, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
              · rcases m.htr 1 2 4 (by decide) (by decide) with h550 | h550
                · linarith only [h0, h346, h550, hc12, hlam, hphi, u1ehi0]
                · linarith only [h549, h550, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h549, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
