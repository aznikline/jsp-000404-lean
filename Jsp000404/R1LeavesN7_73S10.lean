import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_15_M_IR_L_R_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h11, h12, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h11, h15, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h17, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h10, h11, h17, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h0, h21, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h20, h21, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h0, h20, h24, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                          · linarith only [h0, h10, h26, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h20, h26, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h20, h26, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              rcases p28_3 (m.d 0 1) (by simp) with h32 | h32
                              · rcases p28_3 (m.d 1 2) (by simp) with h33 | h33
                                · linarith only [h0, h33, hlam]
                                · linarith only [h10, h20, h26, h33, h6, h9, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h32, hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              rcases p28_3 (m.d 0 1) (by simp) with h37 | h37
                              · rcases p28_3 (m.d 1 2) (by simp) with h38 | h38
                                · linarith only [h0, h38, hlam]
                                · linarith only [h38, h7, hlam]
                              · linarith only [h37, hlam, p28_0]
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
                              linarith only [h20, h26, h9, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28_1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p28_1, u1ehi3]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p28_1, u1ehi3]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h1, hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h6, hlam, p28_1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [hc13, hlam, hphi, p28_1, u1ehi3]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h0, h10, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p28_1, u1ehi3]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h2, hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h10, hc15, hlam, hphi, p28_1, u1ehi1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h8, hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h10, hlam, p28_1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h3, hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h7, hlam, p28_1]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [h9, hlam, p28_0]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [hc15, hlam, hphi, p28_1, u1ehi3]
                            · have p28_0 := h28c.1
                              have p28_1 := h28c.2.1
                              have p28_2 := h28c.2.2.1
                              have p28_3 := h28c.2.2.2
                              linarith only [hlam, p28_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                    · linarith only [h62, h8, h9, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h0, h6, h65, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                          · linarith only [h0, h62, h64, h65, h67, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · rcases h1bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p69_1, u5ehi2]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              rcases p69_3 (m.d 0 1) (by simp) with h72 | h72
                              · rcases p69_3 (m.d 1 2) (by simp) with h73 | h73
                                · linarith only [h0, h73, hlam]
                                · linarith only [h6, h73, hlam]
                              · linarith only [h72, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              rcases p69_3 (m.d 0 1) (by simp) with h77 | h77
                              · rcases p69_3 (m.d 1 2) (by simp) with h78 | h78
                                · linarith only [h0, h78, hlam]
                                · linarith only [h64, h65, h67, h7, h78, h8, h9, hc34, hc45, hlam, hphi]
                              · linarith only [h77, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              rcases p69_3 (m.d 0 1) (by simp) with h82 | h82
                              · rcases p69_3 (m.d 1 2) (by simp) with h83 | h83
                                · linarith only [h0, h83, hlam]
                                · linarith only [h7, h83, hlam]
                              · linarith only [h82, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h0, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h8, hc12, hlam, hphi, p69_1, u1ehi3]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p69_1, u5ehi1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h6, hlam, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hc13, hlam, hphi, p69_1, u1ehi3]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h9, hlam, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h2, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hc14, hlam, hphi, p69_1, u1ehi1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h8, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h62, hlam, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h3, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h7, hlam, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h7, hc12, hlam, hphi, p69_1, u1ehi2]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p69_1, u1ehi3]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                      · linarith only [h64, h8, h9, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                  · linarith only [h0, h108, h4, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                      · linarith only [h111, h8, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h108, h113, h6, hc12, hlam, hphi, u1ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                          · rcases h1bigk with h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c | h116c
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h7, hc01, hlam, hphi, ht0b, ht5b, p116_1, u5ehi2]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              rcases p116_3 (m.d 0 1) (by simp) with h119 | h119
                              · rcases p116_3 (m.d 1 2) (by simp) with h120 | h120
                                · linarith only [h0, h120, hlam]
                                · linarith only [h120, h6, hlam]
                              · linarith only [h119, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h110, hc01, hlam, hphi, ht0b, ht5b, p116_1, u5ehi4]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              rcases p116_3 (m.d 0 1) (by simp) with h125 | h125
                              · rcases p116_3 (m.d 1 2) (by simp) with h126 | h126
                                · linarith only [h0, h126, hlam]
                                · linarith only [h126, h7, hlam]
                              · linarith only [h125, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h0, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hc12, hlam, hphi, p116_1, u1ehi2]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h0, h110, hc01, hlam, hphi, ht0b, ht5b, p116_1, u5ehi4]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h0, h108, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p116_1, u1ehi2]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h1, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h6, hlam, p116_1]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h8, hlam, p116_1]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h108, hlam, p116_1]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h2, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hc14, hlam, hphi, p116_1, u1ehi1]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h0, h4, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p116_1, u1ehi2]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h0, h108, h4, h5, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p116_1, u1ehi2]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h3, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h7, hlam, p116_1]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hc15, hlam, hphi, p116_1, u1ehi2]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [h110, hlam, p116_0]
                            · have p116_0 := h116c.1
                              have p116_1 := h116c.2.1
                              have p116_2 := h116c.2.2.1
                              have p116_3 := h116c.2.2.2
                              linarith only [hlam, p116_0]
                          · linarith only [h115, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                      · linarith only [h151, h8, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
                        · linarith only [h108, h153, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                          · linarith only [h110, h155, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h155, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
                  · linarith only [h159, h6, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                    · linarith only [h158, h161, h6, h7, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h163 | h163
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                        · linarith only [h159, h164, h6, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                          · linarith only [h161, h163, h164, h166, h6, h7, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h163, h164, h166, h6, h7, hc34, hc45, hlam, hphi]
                      · linarith only [h158, h159, h163, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                  · linarith only [h0, h158, h170, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                      · linarith only [h158, h173, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h0, h158, h170, h172, h175, h4, h5, h6, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                          · rcases h1bigk with h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c | h178c
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              rcases p178_3 (m.d 0 1) (by simp) with h180 | h180
                              · rcases p178_3 (m.d 1 2) (by simp) with h181 | h181
                                · linarith only [h181, hlam, p178_0]
                                · rcases p178_3 (m.d 1 3) (by simp) with h183 | h183
                                  · linarith only [h1, h183, hlam]
                                  · rcases p178_3 (m.d 1 4) (by simp) with h185 | h185
                                    · linarith only [h185, h2, hlam]
                                    · linarith only [h0, h172, h175, h177, h185, h4, h5, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h180, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              rcases p178_3 (m.d 0 1) (by simp) with h189 | h189
                              · rcases p178_3 (m.d 1 2) (by simp) with h190 | h190
                                · linarith only [h0, h190, hlam]
                                · linarith only [h190, h6, hlam]
                              · linarith only [h189, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h172, hc01, hlam, hphi, ht0b, ht5b, p178_1, u5ehi4]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              rcases p178_3 (m.d 0 1) (by simp) with h195 | h195
                              · rcases p178_3 (m.d 1 2) (by simp) with h196 | h196
                                · linarith only [h0, h196, hlam]
                                · rcases p178_3 (m.d 1 3) (by simp) with h198 | h198
                                  · linarith only [h1, h198, hlam]
                                  · rcases p178_3 (m.d 1 4) (by simp) with h200 | h200
                                    · linarith only [h2, h200, hlam]
                                    · linarith only [h172, h200, hlam]
                              · linarith only [h195, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h0, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h0, h175, h177, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p178_1, u1ehi2]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h0, h172, h175, h177, h4, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p178_1, u5ehi4]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h7, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h1, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h6, hlam, p178_1]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h158, hlam, p178_1]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h170, hlam, p178_1]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h2, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hc14, hlam, hphi, p178_1, u1ehi1]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h0, h158, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p178_1, u1ehi2]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h0, h158, h4, h5, hc01, hlam, hphi, ht0b, ht5b, p178_1, u5ehi1]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h3, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hc15, hlam, hphi, p178_1, u1ehi1]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h0, h175, h177, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p178_1, u1ehi2]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [h172, hlam, p178_0]
                            · have p178_0 := h178c.1
                              have p178_1 := h178c.2.1
                              have p178_2 := h178c.2.2.1
                              have p178_3 := h178c.2.2.2
                              linarith only [hlam, p178_0]
                          · linarith only [h158, h177, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                      · linarith only [h158, h225, h6, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h227, h6, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                          · linarith only [h0, h172, h229, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                          · linarith only [h158, h229, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
              · linarith only [h0, h232, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                          · linarith only [h1, h234, h239, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              rcases p241_3 (m.d 0 1) (by simp) with h243 | h243
                              · rcases p241_3 (m.d 1 2) (by simp) with h244 | h244
                                · linarith only [h244, hlam, p241_0]
                                · rcases p241_3 (m.d 1 3) (by simp) with h246 | h246
                                  · linarith only [h1, h246, hlam]
                                  · linarith only [h246, h6, hlam]
                              · linarith only [h243, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h234, h236, h239, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p241_1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h236, h239, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p241_1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              rcases p241_3 (m.d 0 1) (by simp) with h252 | h252
                              · rcases p241_3 (m.d 1 2) (by simp) with h253 | h253
                                · linarith only [h0, h253, hlam]
                                · rcases p241_3 (m.d 1 3) (by simp) with h255 | h255
                                  · linarith only [h1, h255, hlam]
                                  · linarith only [h235, h255, hlam]
                              · linarith only [h252, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h6, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, h232, h236, h238, h239, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p241_1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h232, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h1, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc13, hlam, hphi, p241_1, u1ehi1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, h236, h239, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p241_1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht5b, p241_1, u5ehi1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h2, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc14, hlam, hphi, p241_1, u1ehi1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h234, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h0, h232, h234, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p241_1, u1ehi1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h3, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hc15, hlam, hphi, p241_1, u1ehi1]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h235, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [h236, hlam, p241_0]
                            · have p241_0 := h241c.1
                              have p241_1 := h241c.2.1
                              have p241_2 := h241c.2.2.1
                              have p241_3 := h241c.2.2.2
                              linarith only [hlam, p241_0]
                        · linarith only [h238, h6, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h237, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                          · linarith only [h0, h234, h236, h283, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              rcases p285_3 (m.d 0 1) (by simp) with h287 | h287
                              · rcases p285_3 (m.d 1 2) (by simp) with h288 | h288
                                · linarith only [h288, hlam, p285_0]
                                · rcases p285_3 (m.d 1 3) (by simp) with h290 | h290
                                  · linarith only [h1, h290, hlam]
                                  · linarith only [h290, h6, hlam]
                              · linarith only [h287, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h235, hc01, hlam, hphi, ht0b, ht5b, p285_1, u5ehi3]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              rcases p285_3 (m.d 0 1) (by simp) with h295 | h295
                              · rcases p285_3 (m.d 1 2) (by simp) with h296 | h296
                                · linarith only [h0, h296, hlam]
                                · rcases p285_3 (m.d 1 3) (by simp) with h298 | h298
                                  · linarith only [h1, h298, hlam]
                                  · linarith only [h234, h298, hlam]
                              · linarith only [h295, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              rcases p285_3 (m.d 0 1) (by simp) with h302 | h302
                              · rcases p285_3 (m.d 1 2) (by simp) with h303 | h303
                                · linarith only [h0, h303, hlam]
                                · rcases p285_3 (m.d 1 3) (by simp) with h305 | h305
                                  · linarith only [h1, h305, hlam]
                                  · linarith only [h235, h305, hlam]
                              · linarith only [h302, hlam, p285_0]
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
                              linarith only [h6, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h0, h232, h282, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p285_1, u1ehi3]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h232, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h1, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hc13, hlam, hphi, p285_1, u1ehi1]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p285_1, u1ehi3]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht5b, p285_1, u5ehi1]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h2, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hc14, hlam, hphi, p285_1, u1ehi1]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h234, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h236, hlam, p285_1]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h3, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hc15, hlam, hphi, p285_1, u1ehi1]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h235, hlam, p285_0]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [h0, h232, h282, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p285_1, u1ehi3]
                            · have p285_0 := h285c.1
                              have p285_1 := h285c.2.1
                              have p285_2 := h285c.2.2.1
                              have p285_3 := h285c.2.2.2
                              linarith only [hlam, p285_0]
                        · linarith only [h282, h6, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h0, h235, h281, h4, h5, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h234, h235, h331, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h334 | h334
                        · linarith only [h0, h234, h235, h334, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h334, h6, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h333, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h338 | h338
                  · linarith only [h234, h338, h5, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                      · linarith only [h234, h341, h6, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h0, h341, h4, h5, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                      · linarith only [h0, h234, h344, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                      · linarith only [h344, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
            · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
              · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                · linarith only [h1, h349, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                      · linarith only [h1, h347, h351, h353, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                        · linarith only [h0, h347, h355, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h351, h355, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h349, h351, h352, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h359 | h359
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                      · linarith only [h1, h360, h5, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h362 | h362
                        · linarith only [h347, h351, h362, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h364 | h364
                          · rcases h1bigk with h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h348, hc01, hlam, hphi, ht0b, ht5b, p365_1, u5ehi2]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              rcases p365_3 (m.d 0 1) (by simp) with h368 | h368
                              · rcases p365_3 (m.d 1 2) (by simp) with h369 | h369
                                · linarith only [h0, h369, hlam]
                                · linarith only [h347, h369, hlam]
                              · linarith only [h368, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h359, hc01, hlam, hphi, ht0b, ht5b, p365_1, u5ehi4]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              rcases p365_3 (m.d 0 1) (by simp) with h374 | h374
                              · rcases p365_3 (m.d 1 2) (by simp) with h375 | h375
                                · linarith only [h0, h375, hlam]
                                · linarith only [h348, h375, hlam]
                              · linarith only [h374, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h0, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hc12, hlam, hphi, p365_1, u1ehi2]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h0, h359, hc01, hlam, hphi, ht0b, ht5b, p365_1, u5ehi4]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h0, h351, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p365_1, u1ehi2]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h1, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h347, hlam, p365_1]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h349, hlam, p365_1]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h351, hlam, p365_1]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h2, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hc14, hlam, hphi, p365_1, u1ehi1]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p365_1, u1ehi2]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h2, h351, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p365_1, u1ehi2]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h3, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h348, hlam, p365_1]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hc15, hlam, hphi, p365_1, u1ehi2]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [h359, hlam, p365_0]
                            · have p365_0 := h365c.1
                              have p365_1 := h365c.2.1
                              have p365_2 := h365c.2.2.1
                              have p365_3 := h365c.2.2.2
                              linarith only [hlam, p365_0]
                          · linarith only [h1, h364, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
                      · linarith only [h1, h400, h5, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
                        · linarith only [h1, h347, h351, h402, h5, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
                          · linarith only [h349, h359, h404, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                          · linarith only [h1, h404, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                · linarith only [h1, h407, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                  · linarith only [h347, h348, h409, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h411 | h411
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                      · linarith only [h1, h2, h347, h348, h411, h412, h5, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                        · linarith only [h347, h348, h409, h414, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                          · rcases h1bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              rcases p417_3 (m.d 0 1) (by simp) with h419 | h419
                              · rcases p417_3 (m.d 1 2) (by simp) with h420 | h420
                                · linarith only [h420, hlam, p417_0]
                                · rcases p417_3 (m.d 1 3) (by simp) with h422 | h422
                                  · linarith only [h1, h422, hlam]
                                  · rcases p417_3 (m.d 1 4) (by simp) with h424 | h424
                                    · linarith only [h2, h424, hlam]
                                    · linarith only [h411, h424, hc01, hlam, hphi, ht0b, ht5b, p417_1, u5ehi4]
                              · linarith only [h419, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              rcases p417_3 (m.d 0 1) (by simp) with h428 | h428
                              · rcases p417_3 (m.d 1 2) (by simp) with h429 | h429
                                · linarith only [h0, h429, hlam]
                                · linarith only [h347, h429, hlam]
                              · linarith only [h428, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h411, hc01, hlam, hphi, ht0b, ht5b, p417_1, u5ehi4]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              rcases p417_3 (m.d 0 1) (by simp) with h434 | h434
                              · rcases p417_3 (m.d 1 2) (by simp) with h435 | h435
                                · linarith only [h0, h435, hlam]
                                · rcases p417_3 (m.d 1 3) (by simp) with h437 | h437
                                  · linarith only [h1, h437, hlam]
                                  · rcases p417_3 (m.d 1 4) (by simp) with h439 | h439
                                    · linarith only [h2, h439, hlam]
                                    · linarith only [h411, h439, hlam]
                              · linarith only [h434, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h0, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hc12, hlam, hphi, p417_1, u1ehi2]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h348, h411, hlam, p417_1]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h348, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h1, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h347, hlam, p417_1]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h407, hlam, p417_1]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h409, hlam, p417_1]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h2, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hc14, hlam, hphi, p417_1, u1ehi1]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p417_1, u1ehi2]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p417_1, u5ehi1]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h3, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h347, hc15, hlam, hphi, p417_1, u1ehi2]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p417_1, u1ehi2]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [h411, hlam, p417_0]
                            · have p417_0 := h417c.1
                              have p417_1 := h417c.2.1
                              have p417_2 := h417c.2.2.1
                              have p417_3 := h417c.2.2.2
                              linarith only [hlam, p417_0]
                          · linarith only [h1, h416, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                      · linarith only [h1, h464, h5, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                        · linarith only [h0, h347, h466, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                          · linarith only [h411, h468, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h1, h468, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · linarith only [h347, h4, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
          · rcases m.htr 1 2 3 (by decide) (by decide) with h473 | h473
            · linarith only [h0, h4, h473, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h475 | h475
              · rcases m.htr 1 3 4 (by decide) (by decide) with h476 | h476
                · rcases m.htr 1 3 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h479 | h479
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h480 | h480
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h481 | h481
                          · linarith only [h1, h476, h481, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c | h483c
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h475, h480, hc01, hlam, hphi, ht0b, ht5b, p483_1, u5ehi3]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h476, h478, h481, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p483_1]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h478, h481, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p483_1]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              rcases p483_3 (m.d 0 1) (by simp) with h488 | h488
                              · rcases p483_3 (m.d 1 2) (by simp) with h489 | h489
                                · linarith only [h0, h489, hlam]
                                · linarith only [h475, h489, hlam]
                              · linarith only [h488, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h0, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h473, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h0, h478, h481, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p483_1]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hc12, hlam, hphi, p483_1, u1ehi4]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h1, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hc13, hlam, hphi, p483_1, u1ehi1]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h1, h478, h481, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p483_1]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p483_1, u1ehi4]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h2, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h475, h480, hc14, hlam, hphi, ht01, ht0b, ht5b, p483_1, u5ehi3]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h476, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h1, h476, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p483_1, u1ehi4]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h3, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h475, hlam, p483_1]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h477, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [h478, hlam, p483_0]
                            · have p483_0 := h483c.1
                              have p483_1 := h483c.2.1
                              have p483_2 := h483c.2.2.1
                              have p483_3 := h483c.2.2.2
                              linarith only [hlam, p483_0]
                        · linarith only [h0, h4, h475, h480, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4, h475, h479, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h517 | h517
                          · linarith only [h1, h476, h517, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h475, h516, hc01, hlam, hphi, ht0b, ht5b, p519_1, u5ehi3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h473, h475, h516, hc01, hlam, hphi, ht0b, ht5b, p519_1, u5ehi3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              rcases p519_3 (m.d 0 1) (by simp) with h523 | h523
                              · rcases p519_3 (m.d 1 2) (by simp) with h524 | h524
                                · linarith only [h0, h524, hlam]
                                · linarith only [h475, h516, h524, hc01, hlam, hphi, ht0b, ht5b, p519_1, u5ehi3]
                              · linarith only [h523, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              rcases p519_3 (m.d 0 1) (by simp) with h528 | h528
                              · rcases p519_3 (m.d 1 2) (by simp) with h529 | h529
                                · linarith only [h0, h529, hlam]
                                · linarith only [h475, h529, hlam]
                              · linarith only [h528, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h473, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hc12, hlam, hphi, p519_1, u1ehi3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h1, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h475, hc13, hlam, hphi, ht01, ht0b, ht5b, p519_1, u5ehi2]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p519_1, u1ehi3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p519_1, u1ehi4]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h2, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h475, h516, hc14, hlam, hphi, ht01, ht0b, ht5b, p519_1, u5ehi3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h476, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h478, hlam, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h3, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h475, hlam, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h477, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hc15, hlam, hphi, p519_1, u1ehi3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                        · linarith only [h0, h4, h475, h516, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4, h475, h515, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h473, h475, h477, hlam]
                · linarith only [h472, h473, h475, h476, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
                · rcases m.htr 1 3 5 (by decide) (by decide) with h558 | h558
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h561 | h561
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h562 | h562
                          · linarith only [h1, h557, h562, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              rcases p564_3 (m.d 0 1) (by simp) with h566 | h566
                              · rcases p564_3 (m.d 1 2) (by simp) with h567 | h567
                                · linarith only [h567, hlam, p564_0]
                                · rcases p564_3 (m.d 1 3) (by simp) with h569 | h569
                                  · linarith only [h1, h569, hlam]
                                  · linarith only [h473, h569, hlam]
                              · linarith only [h566, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h557, h559, h562, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p564_1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h559, h562, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p564_1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              rcases p564_3 (m.d 0 1) (by simp) with h575 | h575
                              · rcases p564_3 (m.d 1 2) (by simp) with h576 | h576
                                · linarith only [h0, h576, hlam]
                                · rcases p564_3 (m.d 1 3) (by simp) with h578 | h578
                                  · linarith only [h1, h578, hlam]
                                  · linarith only [h558, h578, hlam]
                              · linarith only [h575, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h0, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h473, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h0, h559, h562, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p564_1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h475, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h1, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hc13, hlam, hphi, p564_1, u1ehi1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h1, h559, h562, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p564_1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p564_1, u5ehi1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h2, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hc14, hlam, hphi, p564_1, u1ehi1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h557, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h1, h475, h557, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p564_1, u1ehi1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h3, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hc15, hlam, hphi, p564_1, u1ehi1]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h558, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [h559, hlam, p564_0]
                            · have p564_0 := h564c.1
                              have p564_1 := h564c.2.1
                              have p564_2 := h564c.2.2.1
                              have p564_3 := h564c.2.2.2
                              linarith only [hlam, p564_0]
                        · linarith only [h0, h4, h561, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h0, h4, h560, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h606 | h606
                          · linarith only [h1, h557, h559, h606, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              rcases p608_3 (m.d 0 1) (by simp) with h610 | h610
                              · rcases p608_3 (m.d 1 2) (by simp) with h611 | h611
                                · linarith only [h611, hlam, p608_0]
                                · rcases p608_3 (m.d 1 3) (by simp) with h613 | h613
                                  · linarith only [h1, h613, hlam]
                                  · linarith only [h473, h613, hlam]
                              · linarith only [h610, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h558, hc01, hlam, hphi, ht0b, ht5b, p608_1, u5ehi3]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              rcases p608_3 (m.d 0 1) (by simp) with h618 | h618
                              · rcases p608_3 (m.d 1 2) (by simp) with h619 | h619
                                · linarith only [h0, h619, hlam]
                                · rcases p608_3 (m.d 1 3) (by simp) with h621 | h621
                                  · linarith only [h1, h621, hlam]
                                  · linarith only [h557, h621, hlam]
                              · linarith only [h618, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              rcases p608_3 (m.d 0 1) (by simp) with h625 | h625
                              · rcases p608_3 (m.d 1 2) (by simp) with h626 | h626
                                · linarith only [h0, h626, hlam]
                                · rcases p608_3 (m.d 1 3) (by simp) with h628 | h628
                                  · linarith only [h1, h628, hlam]
                                  · linarith only [h558, h628, hlam]
                              · linarith only [h625, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h0, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h473, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hc12, hlam, hphi, p608_1, u1ehi3]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h475, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h1, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hc13, hlam, hphi, p608_1, u1ehi1]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p608_1, u1ehi3]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p608_1, u5ehi1]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h2, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hc14, hlam, hphi, p608_1, u1ehi1]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h557, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h559, hlam, p608_1]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h3, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hc15, hlam, hphi, p608_1, u1ehi1]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h558, hlam, p608_0]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [h1, h558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p608_1, u1ehi3]
                            · have p608_0 := h608c.1
                              have p608_1 := h608c.2.1
                              have p608_2 := h608c.2.2.1
                              have p608_3 := h608c.2.2.2
                              linarith only [hlam, p608_0]
                        · linarith only [h1, h4, h558, h605, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h1, h4, h557, h604, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h654 | h654
                    · linarith only [h557, h558, h654, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h657 | h657
                        · linarith only [h558, h657, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h0, h4, h657, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h1, h4, h557, h656, hlam]
                · linarith only [h4, h472, h557, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h662 | h662
            · linarith only [h0, h4, h662, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
              · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                · linarith only [h1, h472, h665, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h667 | h667
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h668 | h668
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h669 | h669
                      · linarith only [h0, h4, h472, h664, h669, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h4, h664, h669, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h662, h664, h665, h668, hlam]
                  · linarith only [h662, h664, h667, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                · linarith only [h0, h4, h472, h674, hc13, hlam, hphi, u1ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h677 | h677
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h678 | h678
                      · linarith only [h1, h472, h676, h678, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h4, h678, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h674, h676, h677, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h683 | h683
                      · linarith only [h0, h4, h472, h683, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h0, h4, h683, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                      · linarith only [h0, h4, h472, h686, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h0, h4, h686, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

end R2N4
