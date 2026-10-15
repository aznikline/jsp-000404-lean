import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                        · linarith only [h0, h10, h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h10, h19, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h10, h13, h19, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h13, h14, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h13, h23, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h13, h26, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h10, h23, h28, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h0, h11, h30, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h2, h25, h26, h30, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h0, h10, h33, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                          · linarith only [h0, h10, h13, h25, h35, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                            · linarith only [h0, h13, h25, h37, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                              · linarith only [h10, h13, h25, h39, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h10, h13, h39, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                · linarith only [h0, h10, h4, h45, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h0, h10, h4, h44, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                        · linarith only [h0, h10, h4, h44, h51, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h10, h44, h47, h51, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h4, h47, h48, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h10, h44, h47, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                · linarith only [h0, h10, h4, h56, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                              · linarith only [h1, h58, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h2, h60, h64, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h44, h60, h63, hlam]
                          · linarith only [h10, h59, h62, hlam]
                        · linarith only [h10, h59, h61, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                            · linarith only [h0, h5, h58, h60, h72, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                              · linarith only [h44, h58, h72, h74, hlam]
                              · rcases h0bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h4, h44, h58, h7, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h44, h58, h7, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h44, h58, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h44, h58, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h0, hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h44, h58, h7, h72, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h0, h44, h58, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h0, h44, h58, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h1, hlam, p76_1]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h4, hlam, p76_1]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h44, h58, h72, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h0, h4, h44, h58, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h2, hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h5, hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h7, hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h0, h4, h44, h58, h7, h72, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p76_1, u3ehi3]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h3, hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h6, hlam, p76_1]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h8, hlam, p76_0]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [h9, hlam, p76_1]
                                · have p76_0 := h76c.1
                                  have p76_1 := h76c.2.1
                                  have p76_2 := h76c.2.2.1
                                  have p76_3 := h76c.2.2.2
                                  linarith only [hlam, p76_0]
                          · linarith only [h10, h59, h71, hlam]
                        · linarith only [h10, h58, h59, h60, h70, h9, hc05, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h58, h59, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                    · linarith only [h0, h105, h4, h58, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                        · linarith only [h0, h108, h4, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                          · linarith only [h0, h108, h110, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                              · rcases h0bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h10, h110, h113, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h10, h110, h113, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h107, h2, hc01, hlam, hphi, ht0b, ht5b, p114_1, u5ehi4]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h10, h110, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h0, hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h10, h110, h113, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h0, h10, h110, h113, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h0, h10, h110, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h1, hlam, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h4, hlam, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h10, h110, h113, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h0, h10, h110, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h2, hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h5, hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h7, hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h10, h110, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h3, hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h6, hlam, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h8, hlam, p114_0]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [h9, hlam, p114_1]
                                · have p114_0 := h114c.1
                                  have p114_1 := h114c.2.1
                                  have p114_2 := h114c.2.2.1
                                  have p114_3 := h114c.2.2.2
                                  linarith only [hlam, p114_0]
                              · linarith only [h107, h113, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h107, h112, h44, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                        · linarith only [h0, h142, h4, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h142, h144, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                            · linarith only [h0, h107, h146, h5, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                              · linarith only [h146, h148, h44, h58, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · linarith only [h148, h58, h9, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h151 | h151
            · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
              · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                · rcases m.htr 1 3 4 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h156, h2, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                        · linarith only [h0, h151, h158, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h158, h7, h9, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h154, h155, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h154, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h0, h151, h153, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h151, h152, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
                · linarith only [h0, h151, h166, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                      · linarith only [h170, h2, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                        · linarith only [h0, h151, h165, h172, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h151, h165, h168, h172, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h168, h169, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h168, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h177 | h177
                · linarith only [h165, h177, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                      · linarith only [h165, h181, h2, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                            · linarith only [h185, h5, h9, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                              · linarith only [h165, h179, h187, h5, h9, hlam]
                              · rcases h0bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h151, h180, h187, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi3]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h151, h180, h187, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi3]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  rcases p189_3 (m.d 0 1) (by simp) with h193 | h193
                                  · rcases p189_3 (m.d 0 2) (by simp) with h194 | h194
                                    · linarith only [h0, h194, hlam]
                                    · linarith only [h194, h5, hlam]
                                  · linarith only [h193, h2, hlam]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  rcases p189_3 (m.d 0 1) (by simp) with h198 | h198
                                  · rcases p189_3 (m.d 0 2) (by simp) with h199 | h199
                                    · linarith only [h0, h199, hlam]
                                    · linarith only [h199, h6, hlam]
                                  · linarith only [h198, h3, hlam]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h0, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h151, h180, h187, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi3]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  rcases p189_3 (m.d 0 1) (by simp) with h206 | h206
                                  · rcases p189_3 (m.d 0 2) (by simp) with h207 | h207
                                    · rcases p189_3 (m.d 0 3) (by simp) with h208 | h208
                                      · linarith only [h208, h4, hlam]
                                      · linarith only [h208, h7, hlam]
                                    · linarith only [h207, h5, hlam]
                                  · linarith only [h2, h206, hlam]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  rcases p189_3 (m.d 0 1) (by simp) with h213 | h213
                                  · rcases p189_3 (m.d 0 2) (by simp) with h214 | h214
                                    · rcases p189_3 (m.d 0 3) (by simp) with h215 | h215
                                      · linarith only [h215, h4, hlam]
                                      · linarith only [h215, h8, hlam]
                                    · linarith only [h214, h6, hlam]
                                  · linarith only [h213, h3, hlam]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h1, hlam, p189_1]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h4, hlam, p189_1]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  rcases p189_3 (m.d 0 1) (by simp) with h223 | h223
                                  · rcases p189_3 (m.d 0 2) (by simp) with h224 | h224
                                    · rcases p189_3 (m.d 0 3) (by simp) with h225 | h225
                                      · rcases p189_3 (m.d 0 4) (by simp) with h226 | h226
                                        · linarith only [h226, h7, hlam]
                                        · rcases p189_3 (m.d 0 5) (by simp) with h228 | h228
                                          · linarith only [h228, h8, hlam]
                                          · linarith only [h228, h9, hlam]
                                      · linarith only [h225, h7, hlam]
                                    · linarith only [h224, h5, hlam]
                                  · linarith only [h2, h223, hlam]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  rcases p189_3 (m.d 0 1) (by simp) with h234 | h234
                                  · rcases p189_3 (m.d 0 2) (by simp) with h235 | h235
                                    · rcases p189_3 (m.d 0 3) (by simp) with h236 | h236
                                      · rcases p189_3 (m.d 0 4) (by simp) with h237 | h237
                                        · linarith only [h237, h7, hlam]
                                        · rcases p189_3 (m.d 0 5) (by simp) with h239 | h239
                                          · linarith only [h239, h8, hlam]
                                          · rcases h0emin with h241 | h241 | h241 | h241 | h241
                                            · rcases h2bigk with h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h165, h4, h5, h9, hlam, p189_1, p242_2]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h151, h180, h187, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1, u3ehi3]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                rcases p242_3 (m.d 0 2) (by simp) with h246 | h246
                                                · rcases p242_3 (m.d 1 2) (by simp) with h247 | h247
                                                  · linarith only [h0, h247, hlam]
                                                  · rcases p242_3 (m.d 2 3) (by simp) with h249 | h249
                                                    · linarith only [h249, h4, hlam]
                                                    · linarith only [h183, h249, hlam]
                                                · linarith only [h246, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                rcases p242_3 (m.d 0 2) (by simp) with h253 | h253
                                                · rcases p242_3 (m.d 1 2) (by simp) with h254 | h254
                                                  · linarith only [h0, h254, hlam]
                                                  · rcases p242_3 (m.d 2 3) (by simp) with h256 | h256
                                                    · linarith only [h256, h4, hlam]
                                                    · linarith only [h184, h256, hlam]
                                                · linarith only [h253, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h0, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h151, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h165, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h177, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h4, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                rcases p242_3 (m.d 0 2) (by simp) with h266 | h266
                                                · rcases p242_3 (m.d 1 2) (by simp) with h267 | h267
                                                  · linarith only [h267, hlam, p242_0]
                                                  · rcases p242_3 (m.d 2 3) (by simp) with h269 | h269
                                                    · rcases p242_3 (m.d 2 4) (by simp) with h270 | h270
                                                      · linarith only [h183, h270, hlam]
                                                      · linarith only [h165, h270, hlam]
                                                    · linarith only [h269, hlam, p242_0]
                                                · linarith only [h0, h266, hlam]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h165, hc12, hc23, hlam, hphi, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h0, h177, h179, h181, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1, u3ehi3]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h5, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h5, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h183, hlam, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h185, hlam, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h6, hlam, p242_0]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h184, hlam, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p189_1, p242_1]
                                              · have p242_0 := h242c.1
                                                have p242_1 := h242c.2.1
                                                have p242_2 := h242c.2.2.1
                                                have p242_3 := h242c.2.2.2
                                                linarith only [hlam, p242_0]
                                            · rcases h2bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h165, h4, h5, h9, hlam, p189_1, p288_2]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h0, h151, h180, h187, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p288_1, u3ehi3]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                rcases p288_3 (m.d 0 2) (by simp) with h292 | h292
                                                · rcases p288_3 (m.d 1 2) (by simp) with h293 | h293
                                                  · linarith only [h0, h293, hlam]
                                                  · rcases p288_3 (m.d 2 3) (by simp) with h295 | h295
                                                    · linarith only [h295, h4, hlam]
                                                    · linarith only [h183, h295, hlam]
                                                · linarith only [h292, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                rcases p288_3 (m.d 0 2) (by simp) with h299 | h299
                                                · rcases p288_3 (m.d 1 2) (by simp) with h300 | h300
                                                  · linarith only [h0, h300, hlam]
                                                  · rcases p288_3 (m.d 2 3) (by simp) with h302 | h302
                                                    · linarith only [h302, h4, hlam]
                                                    · linarith only [h184, h302, hlam]
                                                · linarith only [h299, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h0, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h151, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h165, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h177, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h4, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                rcases p288_3 (m.d 0 2) (by simp) with h312 | h312
                                                · rcases p288_3 (m.d 1 2) (by simp) with h313 | h313
                                                  · linarith only [h313, hlam, p288_0]
                                                  · rcases p288_3 (m.d 2 3) (by simp) with h315 | h315
                                                    · rcases p288_3 (m.d 2 4) (by simp) with h316 | h316
                                                      · linarith only [h183, h316, hlam]
                                                      · linarith only [h165, h316, hlam]
                                                    · linarith only [h315, hlam, p288_0]
                                                · linarith only [h0, h312, hlam]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h165, hc12, hc23, hlam, hphi, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p288_1, u5ehi2]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h5, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h0, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h183, hlam, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h185, hlam, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h6, hlam, p288_0]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h184, hlam, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p189_1, p288_1]
                                              · have p288_0 := h288c.1
                                                have p288_1 := h288c.2.1
                                                have p288_2 := h288c.2.2.1
                                                have p288_3 := h288c.2.2.2
                                                linarith only [hlam, p288_0]
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
                                                linarith only [h165, h4, h5, h9, hlam, p189_1, p334_2]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h0, h151, h180, h187, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1, u3ehi3]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                rcases p334_3 (m.d 0 2) (by simp) with h338 | h338
                                                · rcases p334_3 (m.d 1 2) (by simp) with h339 | h339
                                                  · linarith only [h0, h339, hlam]
                                                  · rcases p334_3 (m.d 2 3) (by simp) with h341 | h341
                                                    · linarith only [h341, h4, hlam]
                                                    · linarith only [h183, h341, hlam]
                                                · linarith only [h338, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                rcases p334_3 (m.d 0 2) (by simp) with h345 | h345
                                                · rcases p334_3 (m.d 1 2) (by simp) with h346 | h346
                                                  · linarith only [h0, h346, hlam]
                                                  · rcases p334_3 (m.d 2 3) (by simp) with h348 | h348
                                                    · linarith only [h348, h4, hlam]
                                                    · linarith only [h184, h348, hlam]
                                                · linarith only [h345, hlam, p334_0]
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
                                                linarith only [h151, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h165, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h177, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h4, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                rcases p334_3 (m.d 0 2) (by simp) with h358 | h358
                                                · rcases p334_3 (m.d 1 2) (by simp) with h359 | h359
                                                  · linarith only [h359, hlam, p334_0]
                                                  · rcases p334_3 (m.d 2 3) (by simp) with h361 | h361
                                                    · rcases p334_3 (m.d 2 4) (by simp) with h362 | h362
                                                      · linarith only [h183, h362, hlam]
                                                      · linarith only [h165, h362, hlam]
                                                    · linarith only [h361, hlam, p334_0]
                                                · linarith only [h0, h358, hlam]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h165, hc12, hc23, hlam, hphi, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p334_1, u5ehi2]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h5, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h0, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h183, hlam, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h185, hlam, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h6, hlam, p334_0]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h184, hlam, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p189_1, p334_1]
                                              · have p334_0 := h334c.1
                                                have p334_1 := h334c.2.1
                                                have p334_2 := h334c.2.2.1
                                                have p334_3 := h334c.2.2.2
                                                linarith only [hlam, p334_0]
                                            · linarith only [h0, h241, h4, h9, hc01, hlam, p189_1]
                                            · linarith only [h0, h241, h4, hc01, hlam, p189_1]
                                      · linarith only [h236, h8, hlam]
                                    · linarith only [h235, h6, hlam]
                                  · linarith only [h234, h3, hlam]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h2, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h5, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h7, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h9, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h3, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h6, hlam, p189_1]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h8, hlam, p189_0]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [h179, h2, h9, hc45, hlam, hphi, ht34, p189_1, u3ehi3]
                                · have p189_0 := h189c.1
                                  have p189_1 := h189c.2.1
                                  have p189_2 := h189c.2.2.1
                                  have p189_3 := h189c.2.2.2
                                  linarith only [hlam, p189_0]
                          · linarith only [h1, h180, h184, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h151, h165, h179, h183, h5, h9, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h179, h180, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h179, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
        · linarith only [h400, h7, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
          · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                  · linarith only [h1, h406, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                    · linarith only [h1, h400, h408, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                        · linarith only [h1, h403, h411, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                          · linarith only [h1, h400, h403, h413, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                            · linarith only [h0, h404, h415, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · linarith only [h2, h410, h411, h415, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h402, h403, h406, h410, h7, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h403, h405, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h403, h404, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
              · rcases m.htr 1 2 5 (by decide) (by decide) with h422 | h422
                · linarith only [h4, h403, h422, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h424 | h424
                  · linarith only [h4, h403, h424, h7, hlam]
                  · linarith only [h4, h403, h421, h424, h7, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
                · linarith only [h0, h421, h427, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                  · linarith only [h1, h429, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                    · linarith only [h1, h4, h400, h403, h431, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h433 | h433
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
                        · linarith only [h4, h434, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h436 | h436
                          · linarith only [h4, h400, h436, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h438 | h438
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h439 | h439
                              · rcases h0bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h4, h403, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 1) (by simp) with h443 | h443
                                  · rcases p440_3 (m.d 0 2) (by simp) with h444 | h444
                                    · linarith only [h0, h444, hlam]
                                    · linarith only [h4, h444, hlam]
                                  · linarith only [h1, h443, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h421, h433, h5, hc01, hlam, hphi, ht0b, ht5b, p440_1, u5ehi4]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 1) (by simp) with h449 | h449
                                  · rcases p440_3 (m.d 0 2) (by simp) with h450 | h450
                                    · linarith only [h0, h450, hlam]
                                    · linarith only [h450, h6, hlam]
                                  · linarith only [h3, h449, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h0, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 1) (by simp) with h456 | h456
                                  · rcases p440_3 (m.d 0 2) (by simp) with h457 | h457
                                    · rcases p440_3 (m.d 0 3) (by simp) with h458 | h458
                                      · linarith only [h4, h458, hlam]
                                      · rcases p440_3 (m.d 0 4) (by simp) with h460 | h460
                                        · linarith only [h460, h5, hlam]
                                        · linarith only [h460, h7, hlam]
                                    · linarith only [h4, h457, hlam]
                                  · linarith only [h1, h456, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h421, h433, h5, hc02, hlam, hphi, ht0b, ht5b, p440_1, u5ehi4]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 1) (by simp) with h466 | h466
                                  · rcases p440_3 (m.d 0 2) (by simp) with h467 | h467
                                    · rcases p440_3 (m.d 0 3) (by simp) with h468 | h468
                                      · linarith only [h4, h468, hlam]
                                      · rcases p440_3 (m.d 0 4) (by simp) with h470 | h470
                                        · linarith only [h470, h5, hlam]
                                        · linarith only [h402, h470, hlam]
                                    · linarith only [h467, h6, hlam]
                                  · linarith only [h3, h466, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h1, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h4, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h7, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h400, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h2, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h5, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h4, h403, h7, hc12, hc34, hlam, hphi, ht23, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h4, h400, h403, h7, hc12, hc34, hlam, hphi, ht23, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h3, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h6, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h4, h400, h403, hc12, hc35, hlam, hphi, ht23, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h402, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                              · linarith only [h2, h402, h433, h439, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                            · linarith only [h421, h433, h438, hlam]
                      · linarith only [h402, h429, h433, h7, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h493 | h493
            · rcases m.htr 1 2 4 (by decide) (by decide) with h494 | h494
              · rcases m.htr 1 2 5 (by decide) (by decide) with h495 | h495
                · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
                  · linarith only [h1, h496, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h498 | h498
                    · linarith only [h1, h402, h498, h7, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
                      · linarith only [h2, h402, h500, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h502 | h502
                        · linarith only [h1, h402, h493, h502, h7, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h504 | h504
                          · linarith only [h0, h4, h400, h504, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h506 | h506
                            · linarith only [h1, h2, h402, h493, h494, h506, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h508 | h508
                              · linarith only [h402, h5, h502, h508, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h1, h493, h508, h7, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h493, h495, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h493, h494, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
              · linarith only [h4, h402, h493, h513, h7, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                · linarith only [h4, h402, h493, h515, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h517 | h517
                  · linarith only [h4, h493, h517, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
                    · linarith only [h4, h400, h493, h519, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
                      · linarith only [h402, h5, h513, h521, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                        · linarith only [h4, h523, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
                          · linarith only [h4, h400, h525, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                            · linarith only [h402, h5, h527, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h529 | h529
                              · linarith only [h4, h402, h493, h529, h7, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h4, h493, h529, h7, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h532 | h532
      · rcases m.htr 0 3 5 (by decide) (by decide) with h533 | h533
        · linarith only [h4, h533, h6, hlam]
        · linarith only [h532, h533, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h536 | h536
        · linarith only [h532, h536, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
          · linarith only [h5, h538, h6, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
            · rcases m.htr 1 2 4 (by decide) (by decide) with h541 | h541
              · rcases m.htr 1 2 5 (by decide) (by decide) with h542 | h542
                · linarith only [h0, h542, h6, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h544 | h544
                  · linarith only [h1, h532, h544, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h546 | h546
                    · linarith only [h0, h1, h532, h536, h540, h546, h6, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h548 | h548
                      · linarith only [h2, h538, h548, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h550 | h550
                        · linarith only [h0, h540, h550, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h552 | h552
                          · linarith only [h0, h536, h541, h550, h552, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h4, h552, h6, hc35, hlam, hphi, u3ehi2]
              · linarith only [h5, h540, h541, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h4, h540, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h557 | h557
    · rcases m.htr 0 3 4 (by decide) (by decide) with h558 | h558
      · linarith only [h4, h5, h558, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
        · linarith only [h558, h560, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h562 | h562
          · rcases m.htr 1 2 3 (by decide) (by decide) with h563 | h563
            · rcases m.htr 1 2 4 (by decide) (by decide) with h564 | h564
              · linarith only [h0, h5, h564, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                · rcases m.htr 1 3 4 (by decide) (by decide) with h567 | h567
                  · linarith only [h1, h558, h567, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                    · linarith only [h1, h558, h569, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
                        · linarith only [h4, h558, h572, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h4, h5, h572, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h563, h564, h571, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h557, h563, h566, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h4, h5, h563, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h562, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h579 | h579
      · linarith only [h4, h5, h579, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h581 | h581
        · linarith only [h579, h581, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h583 | h583
          · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
            · rcases m.htr 1 2 4 (by decide) (by decide) with h585 | h585
              · linarith only [h0, h5, h585, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h587 | h587
                · linarith only [h0, h557, h587, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h589 | h589
                  · linarith only [h1, h579, h589, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                    · linarith only [h1, h581, h591, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h594 | h594
                        · linarith only [h0, h579, h584, h594, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h5, h584, h594, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h579, h583, h584, h585, h593, hc34, hlam, hphi, u3ehi2]
            · linarith only [h4, h5, h584, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h583, hc45, hlam, hphi, ht34, u3ehi2]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h601 | h601
  · rcases m.htr 0 3 4 (by decide) (by decide) with h602 | h602
    · rcases m.htr 0 3 5 (by decide) (by decide) with h603 | h603
      · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
        · rcases m.htr 1 2 3 (by decide) (by decide) with h605 | h605
          · linarith only [h4, h601, h605, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
            · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
              · rcases m.htr 1 3 4 (by decide) (by decide) with h609 | h609
                · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h614 | h614
                          · linarith only [h0, h4, h607, h614, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · linarith only [h2, h611, h612, h614, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h4, h608, h613, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4, h608, h612, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4, h600, h604, h609, h611, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h4, h603, h605, h608, h610, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h4, h602, h605, h608, h609, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h4, h601, h608, hc12, hc23, hlam, hphi]
            · linarith only [h4, h600, h607, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
          · linarith only [h4, h601, h624, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
            · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                · rcases m.htr 1 3 5 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                    · linarith only [h2, h604, h630, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h632 | h632
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h634 | h634
                          · linarith only [h2, h604, h626, h634, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h636 | h636
                            · linarith only [h2, h604, h626, h632, h636, hlam]
                            · rcases h0bigk with h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c | h638c
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h0, h627, h632, h634, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p638_1, u3ehi3]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h0, h4, h627, h632, h634, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p638_1, u3ehi3]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                rcases p638_3 (m.d 0 1) (by simp) with h642 | h642
                                · rcases p638_3 (m.d 0 2) (by simp) with h643 | h643
                                  · linarith only [h0, h643, hlam]
                                  · linarith only [h600, h643, hlam]
                                · linarith only [h2, h642, hlam]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                rcases p638_3 (m.d 0 1) (by simp) with h647 | h647
                                · rcases p638_3 (m.d 0 2) (by simp) with h648 | h648
                                  · linarith only [h0, h648, hlam]
                                  · linarith only [h601, h648, hlam]
                                · linarith only [h3, h647, hlam]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h0, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h4, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h2, h4, h626, h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p638_1, u3ehi3]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h2, h4, h604, h626, h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p638_1, u3ehi3]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h1, hlam, p638_1]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h0, h627, h632, h634, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p638_1, u3ehi3]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                rcases p638_3 (m.d 0 1) (by simp) with h660 | h660
                                · rcases p638_3 (m.d 0 2) (by simp) with h661 | h661
                                  · linarith only [h4, h661, hlam]
                                  · linarith only [h600, h661, hlam]
                                · linarith only [h2, h660, hlam]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                rcases p638_3 (m.d 0 1) (by simp) with h665 | h665
                                · rcases p638_3 (m.d 0 2) (by simp) with h666 | h666
                                  · linarith only [h4, h666, hlam]
                                  · linarith only [h601, h666, hlam]
                                · linarith only [h3, h665, hlam]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h2, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h600, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h602, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h604, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h3, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h601, hlam, p638_1]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h603, hlam, p638_0]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [h2, h4, h601, h626, h632, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p638_1, u3ehi3]
                              · have p638_0 := h638c.1
                                have p638_1 := h638c.2.1
                                have p638_2 := h638c.2.2.1
                                have p638_3 := h638c.2.2.2
                                linarith only [hlam, p638_0]
                        · linarith only [h0, h4, h627, h633, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h1, h4, h629, h632, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h4, h601, h603, h624, h627, h629, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h602, h624, h627, h628, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h4, h601, h627, hc12, hc23, hlam, hphi]
            · linarith only [h4, h600, h626, hc12, hc23, hlam, hphi]
      · linarith only [h602, h603, hc35, hlam, hphi, u3ehi3]
    · linarith only [h4, h600, h602, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h688 | h688
    · rcases m.htr 0 3 5 (by decide) (by decide) with h689 | h689
      · rcases m.htr 0 4 5 (by decide) (by decide) with h690 | h690
        · linarith only [h600, h601, h690, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h692 | h692
          · linarith only [h0, h4, h692, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
            · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
              · linarith only [h0, h601, h695, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
                · rcases m.htr 1 3 5 (by decide) (by decide) with h698 | h698
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h699 | h699
                    · linarith only [h2, h690, h699, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h701 | h701
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h702 | h702
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h703 | h703
                          · linarith only [h600, h601, h690, h703, hlam]
                          · linarith only [h0, h601, h694, h701, h703, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h0, h4, h694, h701, h702, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h4, h698, h701, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h697, h698, hc35, hlam, hphi, u3ehi3]
                · linarith only [h688, h690, h697, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h600, h601, h694, hc12, hc25, hlam, hphi]
      · linarith only [h688, h689, hc35, hlam, hphi, u3ehi3]
    · linarith only [h4, h600, h688, hlam]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h714 | h714
  · rcases m.htr 0 3 5 (by decide) (by decide) with h715 | h715
    · rcases m.htr 0 4 5 (by decide) (by decide) with h716 | h716
      · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
        · linarith only [h4, h713, h717, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h719 | h719
          · linarith only [h600, h713, h719, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h721 | h721
            · rcases m.htr 1 3 4 (by decide) (by decide) with h722 | h722
              · rcases m.htr 1 3 5 (by decide) (by decide) with h723 | h723
                · rcases m.htr 1 4 5 (by decide) (by decide) with h724 | h724
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h725 | h725
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h726 | h726
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h727 | h727
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h728 | h728
                          · linarith only [h1, h722, h728, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h2, h724, h728, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h600, h722, h724, h727, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h600, h721, h725, h726, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h1, h722, h725, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h714, h716, h719, h721, h724, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h722, h723, hc35, hlam, hphi, u3ehi3]
              · linarith only [h4, h714, h717, h721, h722, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h4, h713, h721, hc12, hc23, hlam, hphi]
      · linarith only [h600, h713, h716, hlam]
    · linarith only [h714, h715, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h740 | h740
    · linarith only [h714, h740, hc34, hlam, hphi, u3ehi4]
    · linarith only [h4, h713, h740, hlam]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  linarith only [h0, h4, h746, hlam]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h748 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  linarith only [h0, h600, h713, h745, h748, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h748 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h750 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  linarith only [h0, h713, h750, hlam]

end R2N4
