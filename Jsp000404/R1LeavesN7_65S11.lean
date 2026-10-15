import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_IR_L_I_L_R_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h10, h11, h12, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h11, h15, h2, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h0, h10, h15, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h10, h19, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h10, h18, h2, h21, h6, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h21, h23, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h2bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, p25_1, u5ehi2]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                rcases p25_3 (m.d 0 2) (by simp) with h28 | h28
                                · rcases p25_3 (m.d 1 2) (by simp) with h29 | h29
                                  · linarith only [h0, h29, hlam]
                                  · linarith only [h29, h7, hlam]
                                · linarith only [h28, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                rcases p25_3 (m.d 0 2) (by simp) with h33 | h33
                                · rcases p25_3 (m.d 1 2) (by simp) with h34 | h34
                                  · linarith only [h0, h34, hlam]
                                  · linarith only [h34, h8, hlam]
                                · linarith only [h33, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                rcases p25_3 (m.d 0 2) (by simp) with h38 | h38
                                · rcases p25_3 (m.d 1 2) (by simp) with h39 | h39
                                  · linarith only [h0, h39, hlam]
                                  · linarith only [h39, h9, hlam]
                                · linarith only [h38, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, hlam, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi4]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h2, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h7, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h10, h2, h6, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h19, hlam, p25_1]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h3, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h8, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h18, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h21, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h4, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h9, hlam, p25_0]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hc25, hlam, hphi, p25_1, u2ehi2]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                              · have p25_0 := h25c.1
                                have p25_1 := h25c.2.1
                                have p25_2 := h25c.2.2.1
                                have p25_3 := h25c.2.2.2
                                linarith only [hlam, p25_0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                        · linarith only [h10, h63, h7, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                          · linarith only [h0, h65, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h65, h67, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h18, h67, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h7, h8, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                · linarith only [h7, h72, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h2, h7, h74, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                            · linarith only [h0, h2, h77, h80, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases h2bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                rcases p82_3 (m.d 0 2) (by simp) with h84 | h84
                                · rcases p82_3 (m.d 1 2) (by simp) with h85 | h85
                                  · linarith only [h0, h85, hlam]
                                  · rcases p82_3 (m.d 2 3) (by simp) with h87 | h87
                                    · linarith only [h2, h87, hlam]
                                    · linarith only [h7, h87, hlam]
                                · linarith only [h0, h84, hlam]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h74, h77, h79, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h74, h79, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, hlam, p82_1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h7, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h72, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h74, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h2, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hc23, hlam, hphi, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h2, h74, h79, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h2, h74, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h3, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hc24, hlam, hphi, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h77, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h2, h74, h77, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h4, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hc25, hlam, hphi, p82_1, u2ehi1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h78, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h79, hlam, p82_1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                          · linarith only [h72, h79, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h1, h76, h78, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h2, h5, h7, h76, h77, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h0, h118, h2, h7, h76, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                        · linarith only [h0, h118, h2, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · linarith only [h117, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                    · linarith only [h1, h125, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                        · linarith only [h1, h122, h128, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                          · linarith only [h0, h122, h127, h130, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h130, h132, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h2bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h0, h124, h127, h128, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u2ehi3]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                rcases p134_3 (m.d 0 2) (by simp) with h137 | h137
                                · rcases p134_3 (m.d 1 2) (by simp) with h138 | h138
                                  · linarith only [h0, h138, hlam]
                                  · linarith only [h122, h138, hlam]
                                · linarith only [h137, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                rcases p134_3 (m.d 0 2) (by simp) with h142 | h142
                                · rcases p134_3 (m.d 1 2) (by simp) with h143 | h143
                                  · linarith only [h0, h143, hlam]
                                  · linarith only [h123, h143, hlam]
                                · linarith only [h142, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                rcases p134_3 (m.d 0 2) (by simp) with h147 | h147
                                · rcases p134_3 (m.d 1 2) (by simp) with h148 | h148
                                  · linarith only [h0, h148, hlam]
                                  · linarith only [h124, h148, hlam]
                                · linarith only [h147, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h0, hlam, p134_1]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h0, h127, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u2ehi3]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u2ehi3]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h0, h127, h128, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u2ehi3]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h2, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h122, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hc23, hlam, hphi, p134_1, u2ehi3]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h128, hlam, p134_1]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h3, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h123, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h127, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h130, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h4, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h124, hlam, p134_0]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hc25, hlam, hphi, p134_1, u2ehi2]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [h0, h124, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, u2ehi3]
                              · have p134_0 := h134c.1
                                have p134_1 := h134c.2.1
                                have p134_2 := h134c.2.2.1
                                have p134_3 := h134c.2.2.2
                                linarith only [hlam, p134_0]
                      · linarith only [h127, h5, h6, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h122, h124, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h122, h123, hc24, hlam, hphi, u2ehi2]
              · linarith only [h122, h2, h6, hc35, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
            · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
              · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h0, h177, h181, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h0, h178, h181, h183, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h180, h183, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h176, h180, h5, hc13, hc34, hlam, hphi]
                  · linarith only [h178, h179, hc25, hlam, hphi, u2ehi3]
                · linarith only [h177, h178, hc24, hlam, hphi, u2ehi2]
              · linarith only [h177, h2, h5, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
              · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                    · linarith only [h1, h176, h193, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h1, h190, h195, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h176, h190, h197, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                          · linarith only [h0, h191, h199, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                            · linarith only [h199, h201, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h1, h190, h201, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h190, h192, hc25, hlam, hphi, u2ehi2]
                · linarith only [h190, h191, hc24, hlam, hphi, u2ehi2]
              · linarith only [h190, h2, h5, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
      · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h209 | h209
      · linarith only [h2, h209, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h211 | h211
        · linarith only [h2, h211, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h213 | h213
          · rcases m.htr 0 3 5 (by decide) (by decide) with h214 | h214
            · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
              · linarith only [h0, h2, h215, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                · linarith only [h0, h209, h217, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h0, h211, h219, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h223 | h223
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                            · rcases h2bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h211, h224, hc24, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h2, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h209, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h211, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h0, hlam, p226_1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h215, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h217, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h219, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hc23, hlam, hphi, p226_1, u2ehi0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hc23, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hc23, hlam, hphi, p226_1, u2ehi3]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h0, h211, hc23, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h0, hc24, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hc24, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h222, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h0, h211, h222, hc23, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h0, hc25, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hc25, hlam, hphi, p226_1, u2ehi1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h223, hlam, p226_0]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [h224, hlam, p226_1]
                              · have p226_0 := h226c.1
                                have p226_1 := h226c.2.1
                                have p226_2 := h226c.2.2.1
                                have p226_3 := h226c.2.2.2
                                linarith only [hlam, p226_0]
                            · rcases h2bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h2, hc23, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h2, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h209, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h211, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h0, hlam, p252_1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h215, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h217, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h219, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hc23, hlam, hphi, p252_1, u2ehi0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hc23, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h224, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p252_1, u5ehi4]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h0, h211, hc23, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h0, hc24, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hc24, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h222, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h0, h211, h222, hc23, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h0, hc25, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hc25, hlam, hphi, p252_1, u2ehi1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h223, hlam, p252_0]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [h224, hlam, p252_1]
                              · have p252_0 := h252c.1
                                have p252_1 := h252c.2.1
                                have p252_2 := h252c.2.2.1
                                have p252_3 := h252c.2.2.2
                                linarith only [hlam, p252_0]
                          · linarith only [h0, h209, h224, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h1, h2, h214, h221, h223, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h2, h213, h222, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h2, h214, h215, h221, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h282 | h282
              · linarith only [h0, h209, h282, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
                · linarith only [h0, h209, h213, h214, h284, hc35, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                  · linarith only [h0, h209, h213, h214, h286, hc35, hlam, hphi, ht23, u2ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h1, h209, h213, h214, h288, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                        · linarith only [h0, h209, h213, h214, h291, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h2, h291, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h2, h213, h290, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h295 | h295
            · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
              · linarith only [h0, h209, h296, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                · linarith only [h0, h209, h298, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h300 | h300
                  · linarith only [h0, h211, h300, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                      · linarith only [h211, h213, h295, h303, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h0, h2, h303, hc34, hlam, hphi, ht23, u2ehi1]
                    · linarith only [h213, h295, h302, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
              · linarith only [h0, h2, h307, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h309 | h309
                · linarith only [h0, h209, h309, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h311 | h311
                  · linarith only [h0, h211, h311, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                    · linarith only [h1, h295, h313, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                      · linarith only [h0, h2, h213, h315, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h2, h315, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h318 | h318
    · linarith only [h0, h1, h318, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h320 | h320
      · linarith only [h318, h320, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h322 | h322
        · linarith only [h318, h322, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h324 | h324
          · rcases m.htr 0 3 5 (by decide) (by decide) with h325 | h325
            · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
              · linarith only [h0, h318, h326, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h0, h1, h326, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h325, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h324, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_22_13_15_M_IR_L_I_L_R_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h331 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h332 | h332
  · rcases m.htr 0 2 4 (by decide) (by decide) with h333 | h333
    · rcases m.htr 0 2 5 (by decide) (by decide) with h334 | h334
      · rcases m.htr 0 3 4 (by decide) (by decide) with h335 | h335
        · rcases m.htr 0 3 5 (by decide) (by decide) with h336 | h336
          · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
            · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
              · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 1 3 5 (by decide) (by decide) with h340 | h340
                  · linarith only [h0, h331, h340, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h331, h336, h337, h340, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h331, h337, h339, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h331, h333, h337, h338, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h0, h331, h336, h337, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
            · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
              · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                · rcases m.htr 1 3 5 (by decide) (by decide) with h349 | h349
                  · linarith only [h0, h331, h336, h349, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h351 | h351
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h352 | h352
                      · linarith only [h0, h331, h334, h336, h346, h352, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                        · linarith only [h0, h331, h346, h351, h354, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                          · linarith only [h354, h356, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h2bigk with h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h0, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 2) (by simp) with h361 | h361
                              · rcases p358_3 (m.d 1 2) (by simp) with h362 | h362
                                · rcases p358_3 (m.d 2 3) (by simp) with h363 | h363
                                  · linarith only [h363, hlam, p358_0]
                                  · rcases p358_3 (m.d 2 4) (by simp) with h365 | h365
                                    · linarith only [h333, h365, hlam]
                                    · rcases p358_3 (m.d 2 5) (by simp) with h367 | h367
                                      · linarith only [h334, h367, hlam]
                                      · linarith only [h352, h367, hlam]
                                · linarith only [h346, h362, hlam]
                              · linarith only [h361, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 2) (by simp) with h372 | h372
                              · rcases p358_3 (m.d 1 2) (by simp) with h373 | h373
                                · rcases p358_3 (m.d 2 3) (by simp) with h374 | h374
                                  · linarith only [h332, h374, hlam]
                                  · linarith only [h351, h374, hlam]
                                · linarith only [h347, h373, hlam]
                              · linarith only [h372, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 2) (by simp) with h379 | h379
                              · rcases p358_3 (m.d 1 2) (by simp) with h380 | h380
                                · rcases p358_3 (m.d 2 3) (by simp) with h381 | h381
                                  · linarith only [h332, h381, hlam]
                                  · rcases p358_3 (m.d 2 4) (by simp) with h383 | h383
                                    · linarith only [h333, h383, hlam]
                                    · rcases p358_3 (m.d 2 5) (by simp) with h385 | h385
                                      · linarith only [h385, hlam, p358_0]
                                      · rcases h3bigk with h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c | h387c
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h336, h356, hc13, hc45, hlam, hphi, ht34, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h336, h356, hc23, hc45, hlam, hphi, ht34, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h336, h356, hc34, hc45, hlam, hphi, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h336, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h331, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h0, h331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p387_1, u2ehi2]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h0, h331, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h349, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h332, hlam, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h346, hlam, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h332, h336, h356, hc34, hc45, hlam, hphi, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h352, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h335, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h335, h336, h356, hc13, hc45, hlam, hphi, ht34, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h351, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h356, hlam, p387_0]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h335, h356, hc34, hc45, hlam, hphi, p387_1]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h346, h356, hc45, hlam, hphi, ht23, ht34, p387_1, u2ehi2]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [h351, h356, hc45, hlam, hphi, ht23, ht34, p387_1, u2ehi3]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          rcases p387_3 (m.d 0 3) (by simp) with h411 | h411
                                          · linarith only [h336, h411, hlam]
                                          · linarith only [h335, h411, hlam]
                                        · have p387_0 := h387c.1
                                          have p387_1 := h387c.2.1
                                          have p387_2 := h387c.2.2.1
                                          have p387_3 := h387c.2.2.2
                                          linarith only [hlam, p387_0]
                                · linarith only [h348, h380, hlam]
                              · linarith only [h379, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h0, h331, h346, h351, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p358_1, u2ehi3]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 2) (by simp) with h419 | h419
                              · linarith only [h0, h419, hlam]
                              · linarith only [h332, h419, hlam]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 2) (by simp) with h422 | h422
                              · linarith only [h0, h422, hlam]
                              · linarith only [h333, h422, hlam]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              rcases p358_3 (m.d 0 2) (by simp) with h425 | h425
                              · linarith only [h0, h425, hlam]
                              · linarith only [h334, h425, hlam]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h332, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h346, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h331, h346, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p358_1, u2ehi3]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h352, hlam, p358_1]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h333, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h347, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h351, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h354, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h334, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h348, hlam, p358_0]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hc25, hlam, hphi, p358_1, u2ehi2]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [h0, h334, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p358_1, u2ehi3]
                            · have p358_0 := h358c.1
                              have p358_1 := h358c.2.1
                              have p358_2 := h358c.2.2.1
                              have p358_3 := h358c.2.2.2
                              linarith only [hlam, p358_0]
                    · linarith only [h0, h331, h335, h351, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h334, h348, hlam]
              · linarith only [h0, h334, h347, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h331, h332, h346, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h447 | h447
          · rcases m.htr 1 2 3 (by decide) (by decide) with h448 | h448
            · rcases m.htr 1 2 4 (by decide) (by decide) with h449 | h449
              · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
                · rcases m.htr 1 3 5 (by decide) (by decide) with h451 | h451
                  · linarith only [h0, h331, h451, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h335, h447, h451, hc13, hc34, hlam, hphi]
                · linarith only [h0, h334, h335, h447, h450, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h331, h333, h448, h449, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h0, h333, h448, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
            · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                  · linarith only [h331, h447, h460, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h462 | h462
                    · linarith only [h331, h335, h457, h462, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                      · linarith only [h331, h447, h457, h464, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h466 | h466
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                          · rcases h2bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              rcases p468_3 (m.d 0 2) (by simp) with h471 | h471
                              · rcases p468_3 (m.d 1 2) (by simp) with h472 | h472
                                · rcases p468_3 (m.d 2 3) (by simp) with h473 | h473
                                  · linarith only [h473, hlam, p468_0]
                                  · rcases p468_3 (m.d 2 4) (by simp) with h475 | h475
                                    · linarith only [h333, h475, hlam]
                                    · linarith only [h462, h475, hlam]
                                · linarith only [h457, h472, hlam]
                              · linarith only [h471, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h466, hc02, hlam, hphi, ht0b, ht5b, p468_1, u5ehi4]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              rcases p468_3 (m.d 0 2) (by simp) with h481 | h481
                              · rcases p468_3 (m.d 1 2) (by simp) with h482 | h482
                                · rcases p468_3 (m.d 2 3) (by simp) with h483 | h483
                                  · linarith only [h332, h483, hlam]
                                  · rcases p468_3 (m.d 2 4) (by simp) with h485 | h485
                                    · linarith only [h333, h485, hlam]
                                    · linarith only [h466, h485, hlam]
                                · linarith only [h459, h482, hlam]
                              · linarith only [h481, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h332, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p468_1, u2ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              rcases p468_3 (m.d 0 2) (by simp) with h492 | h492
                              · linarith only [h0, h492, hlam]
                              · linarith only [h332, h492, hlam]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h466, hc12, hlam, hphi, ht01, ht0b, ht5b, p468_1, u5ehi4]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              rcases p468_3 (m.d 0 2) (by simp) with h496 | h496
                              · linarith only [h0, h496, hlam]
                              · linarith only [h334, h496, hlam]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h332, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h457, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h462, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h464, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h333, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h458, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h333, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p468_1, u2ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h0, h333, h464, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p468_1, u2ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h334, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h459, hlam, p468_0]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hc25, hlam, hphi, p468_1, u2ehi2]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [h466, hlam, p468_1]
                            · have p468_0 := h468c.1
                              have p468_1 := h468c.2.1
                              have p468_2 := h468c.2.2.1
                              have p468_3 := h468c.2.2.2
                              linarith only [hlam, p468_0]
                          · linarith only [h331, h335, h457, h467, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                          · linarith only [h466, h515, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h331, h335, h457, h515, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h331, h457, h459, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h331, h457, h458, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h334, h457, hc23, hlam, hphi, u2ehi4]
      · linarith only [h333, h334, hc25, hlam, hphi, u2ehi3]
    · linarith only [h332, h333, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h331, h332, hlam]

end R2N4
