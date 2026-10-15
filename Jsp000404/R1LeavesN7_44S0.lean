import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6248000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_I_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
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
                        · linarith only [h0, h10, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h10, h19, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h10, h13, h19, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h13, h14, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h13, h23, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                        · linarith only [h13, h26, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h0, h10, h23, h28, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h0, h11, h30, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h2, h25, h30, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h10, h13, h25, h33, h4, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                          · linarith only [h23, h35, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                            · linarith only [h11, h25, h37, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                              · linarith only [h25, h39, h4, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · linarith only [h10, h13, h39, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h12, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h10, h11, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h10, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
            · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
              · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h2, h50, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                        · linarith only [h0, h45, h52, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h48, h52, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h48, h49, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h4, h48, h56, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h2, h58, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                        · linarith only [h4, h48, h60, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h45, h56, h62, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                            · linarith only [h45, h48, h64, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                              · linarith only [h66, h7, h9, hlam]
                              · rcases h0bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h66, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h66, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h0, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h66, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo1]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h66, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h1, hlam, p68_1]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h4, hlam, p68_1]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo2]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h4, h45, h48, h66, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h2, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h5, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h7, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h9, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h3, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h6, hlam, p68_1]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h8, hlam, p68_0]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [h45, h48, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo4]
                                · have p68_0 := h68c.1
                                  have p68_1 := h68c.2.1
                                  have p68_2 := h68c.2.2.1
                                  have p68_3 := h68c.2.2.2
                                  linarith only [hlam, p68_0]
                · linarith only [h47, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h45, h46, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h4, h45, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
          · linarith only [h7, h8, h97, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
            · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h1, h103, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                      · linarith only [h1, h102, h105, h2, h8, h97, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                        · linarith only [h0, h107, h99, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h102, h107, h8, hc23, hc35, hlam, hphi]
                  · linarith only [h102, h7, h8, hc13, hc35, hlam, hphi]
                · linarith only [h101, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h100, h5, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h4, h99, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
        · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
          · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
            · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
              · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                  · linarith only [h1, h119, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                        · linarith only [h1, h116, h121, h123, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h0, h117, h123, h125, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1, h121, h125, h7, hc23, hc34, hlam, hphi]
                      · linarith only [h115, h119, h121, h122, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h114, h121, h7, hc13, hc34, hlam, hphi]
                · linarith only [h118, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h116, h117, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h116, h4, hc12, hlam, hphi, u2elo0]
          · linarith only [h114, h115, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
          · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
            · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
              · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                  · linarith only [h1, h138, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                    · linarith only [h1, h114, h140, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                        · linarith only [h1, h135, h143, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h145 | h145
                          · linarith only [h1, h114, h135, h145, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                            · linarith only [h0, h136, h147, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h142, h147, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                        · linarith only [h1, h134, h135, h142, h150, h7, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                          · linarith only [h114, h134, h135, h138, h142, h152, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                            · linarith only [h136, h142, h154, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                              · rcases h0bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, h138, h142, h5, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u0elo0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  rcases p157_3 (m.d 0 1) (by simp) with h160 | h160
                                  · rcases p157_3 (m.d 0 2) (by simp) with h161 | h161
                                    · linarith only [h0, h161, hlam]
                                    · linarith only [h161, h4, hlam]
                                  · linarith only [h1, h160, hlam]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, h135, h138, h142, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u0elo0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, h135, h138, h142, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u0elo0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h0, hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  rcases p157_3 (m.d 0 1) (by simp) with h169 | h169
                                  · rcases p157_3 (m.d 0 2) (by simp) with h170 | h170
                                    · rcases p157_3 (m.d 0 3) (by simp) with h171 | h171
                                      · linarith only [h171, h4, hlam]
                                      · rcases p157_3 (m.d 0 4) (by simp) with h173 | h173
                                        · linarith only [h173, h5, hlam]
                                        · linarith only [h173, h7, hlam]
                                    · linarith only [h170, h4, hlam]
                                  · linarith only [h1, h169, hlam]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, h135, h138, h142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p157_1, u2elo0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, h135, h138, h142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p157_1, u2elo0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h1, hlam, p157_1]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h4, hlam, p157_1]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h7, hlam, p157_1]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h114, hlam, p157_1]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h2, hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h5, hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  rcases p157_3 (m.d 0 1) (by simp) with h187 | h187
                                  · rcases p157_3 (m.d 0 2) (by simp) with h188 | h188
                                    · rcases p157_3 (m.d 0 3) (by simp) with h189 | h189
                                      · linarith only [h189, h7, hlam]
                                      · rcases p157_3 (m.d 0 4) (by simp) with h191 | h191
                                        · rcases p157_3 (m.d 0 5) (by simp) with h192 | h192
                                          · linarith only [h134, h192, hlam]
                                          · linarith only [h114, h192, hlam]
                                        · linarith only [h191, h7, hlam]
                                    · linarith only [h188, h4, hlam]
                                  · linarith only [h1, h187, hlam]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, h135, h138, h142, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, u0elo3]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h3, hlam, p157_0]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h6, hlam, p157_1]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  rcases p157_3 (m.d 0 1) (by simp) with h202 | h202
                                  · rcases p157_3 (m.d 0 2) (by simp) with h203 | h203
                                    · rcases p157_3 (m.d 0 3) (by simp) with h204 | h204
                                      · linarith only [h114, h204, hlam]
                                      · rcases p157_3 (m.d 0 4) (by simp) with h206 | h206
                                        · rcases p157_3 (m.d 0 5) (by simp) with h207 | h207
                                          · rcases h3bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h135, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, p208_1, u0elo4]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1, p208_1, u0elo0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h7, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h114, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h1, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h138, h142, hc23, hc45, hlam, hphi, ht34, p208_1]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h138, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h140, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h4, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h135, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h150, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h152, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              rcases p208_3 (m.d 0 3) (by simp) with h224 | h224
                                              · linarith only [h224, hlam, p208_0]
                                              · rcases p208_3 (m.d 1 3) (by simp) with h226 | h226
                                                · linarith only [h138, h226, hlam]
                                                · rcases p208_3 (m.d 2 3) (by simp) with h228 | h228
                                                  · linarith only [h150, h228, hlam]
                                                  · rcases p208_3 (m.d 3 4) (by simp) with h230 | h230
                                                    · rcases p208_3 (m.d 3 5) (by simp) with h231 | h231
                                                      · linarith only [h156, h231, hlam]
                                                      · linarith only [h114, h231, hlam]
                                                    · linarith only [h230, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              rcases p208_3 (m.d 0 3) (by simp) with h235 | h235
                                              · linarith only [h235, h7, hlam]
                                              · linarith only [h1, h235, hlam]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              rcases p208_3 (m.d 0 3) (by simp) with h238 | h238
                                              · linarith only [h238, h7, hlam]
                                              · linarith only [h238, h4, hlam]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h114, hc03, hc34, hlam, hphi, p157_1, p208_1]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              rcases p208_3 (m.d 0 3) (by simp) with h243 | h243
                                              · linarith only [h243, hlam, p208_0]
                                              · rcases p208_3 (m.d 1 3) (by simp) with h245 | h245
                                                · linarith only [h140, h245, hlam]
                                                · rcases p208_3 (m.d 2 3) (by simp) with h247 | h247
                                                  · linarith only [h152, h247, hlam]
                                                  · rcases p208_3 (m.d 3 4) (by simp) with h249 | h249
                                                    · rcases p208_3 (m.d 3 5) (by simp) with h250 | h250
                                                      · rcases h5bigk with h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c | h251c
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          rcases p251_3 (m.d 0 5) (by simp) with h253 | h253
                                                          · rcases p251_3 (m.d 1 5) (by simp) with h254 | h254
                                                            · linarith only [h254, h3, hlam]
                                                            · rcases p251_3 (m.d 2 5) (by simp) with h256 | h256
                                                              · linarith only [h256, h6, hlam]
                                                              · rcases p251_3 (m.d 3 5) (by simp) with h258 | h258
                                                                · rcases p251_3 (m.d 4 5) (by simp) with h259 | h259
                                                                  · linarith only [h134, h259, hlam]
                                                                  · linarith only [h142, h259, hlam]
                                                                · linarith only [h140, h258, hlam]
                                                          · linarith only [h253, h3, hlam]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          rcases p251_3 (m.d 0 5) (by simp) with h264 | h264
                                                          · rcases p251_3 (m.d 1 5) (by simp) with h265 | h265
                                                            · linarith only [h265, h3, hlam]
                                                            · linarith only [h137, h265, hlam]
                                                          · linarith only [h264, h6, hlam]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h114, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h134, h135, h138, h142, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p251_1, u2elo0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h3, hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h3, hc25, hlam, hphi, ht0b, ht5b, p251_1, u0elo0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h140, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h142, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h6, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h137, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h152, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h154, hlam, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [hc03, hc35, hlam, hphi, p157_1, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          rcases p251_3 (m.d 0 5) (by simp) with h282 | h282
                                                          · linarith only [h114, h282, hlam]
                                                          · linarith only [h282, h3, hlam]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          rcases p251_3 (m.d 0 5) (by simp) with h285 | h285
                                                          · linarith only [h114, h285, hlam]
                                                          · linarith only [h285, h6, hlam]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h135, h138, h142, h156, hc23, hc34, hlam, hphi, p251_1]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h134, hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h134, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p251_1, u2elo0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h134, h154, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p251_1, u2elo0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [h156, hlam, p251_0]
                                                        · have p251_0 := h251c.1
                                                          have p251_1 := h251c.2.1
                                                          have p251_2 := h251c.2.2.1
                                                          have p251_3 := h251c.2.2.2
                                                          linarith only [hlam, p251_0]
                                                      · linarith only [h250, hlam, p208_0]
                                                    · linarith only [h249, h7, hlam]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              rcases p208_3 (m.d 0 3) (by simp) with h297 | h297
                                              · linarith only [h114, h297, hlam]
                                              · linarith only [h1, h297, hlam]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              rcases p208_3 (m.d 0 3) (by simp) with h300 | h300
                                              · linarith only [h114, h300, hlam]
                                              · linarith only [h300, h4, hlam]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [h156, hlam, p208_0]
                                            · have p208_0 := h208c.1
                                              have p208_1 := h208c.2.1
                                              have p208_2 := h208c.2.2.1
                                              have p208_3 := h208c.2.2.2
                                              linarith only [hlam, p208_0]
                                          · linarith only [h114, h207, hlam]
                                        · linarith only [h206, h7, hlam]
                                    · linarith only [h203, h4, hlam]
                                  · linarith only [h1, h202, hlam]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [h134, hlam, p157_1]
                                · have p157_0 := h157c.1
                                  have p157_1 := h157c.2.1
                                  have p157_2 := h157c.2.2.1
                                  have p157_3 := h157c.2.2.2
                                  linarith only [hlam, p157_0]
                              · linarith only [h1, h134, h135, h156, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h137, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h135, h136, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h135, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
            · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
              · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 3 4 (by decide) (by decide) with h318 | h318
                  · linarith only [h1, h318, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
                    · linarith only [h1, h114, h320, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
                      · linarith only [h134, h2, h322, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                        · linarith only [h1, h315, h324, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h326 | h326
                          · linarith only [h0, h114, h316, h324, h326, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h328 | h328
                            · linarith only [h1, h134, h315, h316, h328, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                              · rcases h0bigk with h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1, u0elo0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 1) (by simp) with h334 | h334
                                  · rcases p331_3 (m.d 0 2) (by simp) with h335 | h335
                                    · linarith only [h0, h335, hlam]
                                    · linarith only [h335, h4, hlam]
                                  · linarith only [h1, h334, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 1) (by simp) with h339 | h339
                                  · rcases p331_3 (m.d 0 2) (by simp) with h340 | h340
                                    · linarith only [h0, h340, hlam]
                                    · linarith only [h340, h5, hlam]
                                  · linarith only [h2, h339, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 1) (by simp) with h344 | h344
                                  · rcases p331_3 (m.d 0 2) (by simp) with h345 | h345
                                    · linarith only [h0, h345, hlam]
                                    · linarith only [h345, h6, hlam]
                                  · linarith only [h3, h344, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h0, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 1) (by simp) with h351 | h351
                                  · rcases p331_3 (m.d 0 2) (by simp) with h352 | h352
                                    · rcases p331_3 (m.d 0 3) (by simp) with h353 | h353
                                      · linarith only [h353, h4, hlam]
                                      · rcases p331_3 (m.d 0 4) (by simp) with h355 | h355
                                        · linarith only [h355, h5, hlam]
                                        · linarith only [h355, h7, hlam]
                                    · linarith only [h352, h4, hlam]
                                  · linarith only [h1, h351, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 1) (by simp) with h360 | h360
                                  · rcases p331_3 (m.d 0 2) (by simp) with h361 | h361
                                    · rcases p331_3 (m.d 0 3) (by simp) with h362 | h362
                                      · linarith only [h362, h4, hlam]
                                      · rcases p331_3 (m.d 0 4) (by simp) with h364 | h364
                                        · linarith only [h364, h5, hlam]
                                        · rcases p331_3 (m.d 0 5) (by simp) with h366 | h366
                                          · linarith only [h366, h6, hlam]
                                          · linarith only [h134, h366, hlam]
                                    · linarith only [h361, h5, hlam]
                                  · linarith only [h2, h360, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 1) (by simp) with h371 | h371
                                  · rcases p331_3 (m.d 0 2) (by simp) with h372 | h372
                                    · rcases p331_3 (m.d 0 3) (by simp) with h373 | h373
                                      · linarith only [h373, h4, hlam]
                                      · rcases p331_3 (m.d 0 4) (by simp) with h375 | h375
                                        · linarith only [h375, h5, hlam]
                                        · rcases p331_3 (m.d 0 5) (by simp) with h377 | h377
                                          · linarith only [h377, h6, hlam]
                                          · rcases h3bigk with h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h134, h315, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p331_1, p379_1, u0elo1]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h134, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p331_1, p379_1, u2elo0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h7, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h114, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h1, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p379_1, u0elo0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h318, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h320, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h4, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h315, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h324, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h326, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              rcases p379_3 (m.d 0 3) (by simp) with h395 | h395
                                              · linarith only [h395, hlam, p379_0]
                                              · rcases p379_3 (m.d 1 3) (by simp) with h397 | h397
                                                · linarith only [h318, h397, hlam]
                                                · rcases p379_3 (m.d 2 3) (by simp) with h399 | h399
                                                  · linarith only [h324, h399, hlam]
                                                  · rcases p379_3 (m.d 3 4) (by simp) with h401 | h401
                                                    · rcases p379_3 (m.d 3 5) (by simp) with h402 | h402
                                                      · linarith only [h330, h402, hlam]
                                                      · linarith only [h114, h402, hlam]
                                                    · linarith only [h401, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              rcases p379_3 (m.d 0 3) (by simp) with h406 | h406
                                              · linarith only [h406, h7, hlam]
                                              · linarith only [h1, h406, hlam]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              rcases p379_3 (m.d 0 3) (by simp) with h409 | h409
                                              · linarith only [h409, h7, hlam]
                                              · linarith only [h4, h409, hlam]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h134, h330, h7, hc03, hc34, hlam, hphi, p379_1]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              rcases p379_3 (m.d 0 3) (by simp) with h414 | h414
                                              · linarith only [h414, hlam, p379_0]
                                              · rcases p379_3 (m.d 1 3) (by simp) with h416 | h416
                                                · linarith only [h320, h416, hlam]
                                                · rcases p379_3 (m.d 2 3) (by simp) with h418 | h418
                                                  · linarith only [h326, h418, hlam]
                                                  · rcases p379_3 (m.d 3 4) (by simp) with h420 | h420
                                                    · rcases p379_3 (m.d 3 5) (by simp) with h421 | h421
                                                      · rcases h5bigk with h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c | h422c
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [hlam, p422_0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h322, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p331_1, p422_1, u2elo0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h324, h328, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p331_1, p422_1, u2elo0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h114, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h134, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h3, hlam, p422_0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [hlam, p422_0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h3, h324, h328, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p422_1, u0elo0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h320, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h322, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h6, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h317, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [hlam, p422_0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h326, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h328, hlam, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          rcases p422_3 (m.d 0 5) (by simp) with h438 | h438
                                                          · linarith only [h114, h438, hlam]
                                                          · rcases p422_3 (m.d 1 5) (by simp) with h440 | h440
                                                            · linarith only [h320, h440, hlam]
                                                            · rcases p422_3 (m.d 2 5) (by simp) with h442 | h442
                                                              · linarith only [h326, h442, hlam]
                                                              · rcases p422_3 (m.d 3 5) (by simp) with h444 | h444
                                                                · rcases p422_3 (m.d 4 5) (by simp) with h445 | h445
                                                                  · linarith only [h330, h445, hlam]
                                                                  · linarith only [h134, h445, hlam]
                                                                · linarith only [h114, h444, hlam]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          rcases p422_3 (m.d 0 5) (by simp) with h449 | h449
                                                          · linarith only [h114, h449, hlam]
                                                          · linarith only [h3, h449, hlam]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          rcases p422_3 (m.d 0 5) (by simp) with h452 | h452
                                                          · linarith only [h114, h452, hlam]
                                                          · linarith only [h452, h6, hlam]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [hlam, p422_0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h134, h7, hc03, hc35, hlam, hphi, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h324, h328, h330, h6, hc23, hc34, hlam, hphi, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h317, h324, h328, h330, hc23, hc34, hlam, hphi, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h324, h328, h330, hc23, hc34, hlam, hphi, p422_1]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [h330, hlam, p422_0]
                                                        · have p422_0 := h422c.1
                                                          have p422_1 := h422c.2.1
                                                          have p422_2 := h422c.2.2.1
                                                          have p422_3 := h422c.2.2.2
                                                          linarith only [hlam, p422_0]
                                                      · linarith only [h421, hlam, p379_0]
                                                    · linarith only [h420, h7, hlam]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              rcases p379_3 (m.d 0 3) (by simp) with h464 | h464
                                              · linarith only [h114, h464, hlam]
                                              · linarith only [h1, h464, hlam]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              rcases p379_3 (m.d 0 3) (by simp) with h467 | h467
                                              · linarith only [h114, h467, hlam]
                                              · linarith only [h4, h467, hlam]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [h330, hlam, p379_0]
                                            · have p379_0 := h379c.1
                                              have p379_1 := h379c.2.1
                                              have p379_2 := h379c.2.2.1
                                              have p379_3 := h379c.2.2.2
                                              linarith only [hlam, p379_0]
                                    · linarith only [h372, h6, hlam]
                                  · linarith only [h3, h371, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h1, hlam, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h4, hlam, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h7, hlam, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h114, hlam, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h2, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h5, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h1, h134, h315, h330, hc23, hc34, hlam, hphi, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h134, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h3, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h6, hlam, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h1, h134, h315, h330, hc23, hc34, hlam, hphi, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h134, h2, h316, h324, h330, hc23, hc34, hlam, hphi, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                              · rcases h0bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h0, h317, h324, h328, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1, u0elo0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h492 | h492
                                  · rcases p489_3 (m.d 0 2) (by simp) with h493 | h493
                                    · linarith only [h0, h493, hlam]
                                    · linarith only [h4, h493, hlam]
                                  · linarith only [h1, h492, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h497 | h497
                                  · rcases p489_3 (m.d 0 2) (by simp) with h498 | h498
                                    · linarith only [h0, h498, hlam]
                                    · linarith only [h498, h5, hlam]
                                  · linarith only [h2, h497, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h502 | h502
                                  · rcases p489_3 (m.d 0 2) (by simp) with h503 | h503
                                    · linarith only [h0, h503, hlam]
                                    · linarith only [h503, h6, hlam]
                                  · linarith only [h3, h502, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h0, hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h509 | h509
                                  · rcases p489_3 (m.d 0 2) (by simp) with h510 | h510
                                    · rcases p489_3 (m.d 0 3) (by simp) with h511 | h511
                                      · linarith only [h4, h511, hlam]
                                      · rcases p489_3 (m.d 0 4) (by simp) with h513 | h513
                                        · linarith only [h5, h513, hlam]
                                        · linarith only [h513, h7, hlam]
                                    · linarith only [h4, h510, hlam]
                                  · linarith only [h1, h509, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h518 | h518
                                  · rcases p489_3 (m.d 0 2) (by simp) with h519 | h519
                                    · rcases p489_3 (m.d 0 3) (by simp) with h520 | h520
                                      · linarith only [h4, h520, hlam]
                                      · rcases p489_3 (m.d 0 4) (by simp) with h522 | h522
                                        · linarith only [h5, h522, hlam]
                                        · rcases p489_3 (m.d 0 5) (by simp) with h524 | h524
                                          · linarith only [h524, h6, hlam]
                                          · linarith only [h134, h524, hlam]
                                    · linarith only [h5, h519, hlam]
                                  · linarith only [h2, h518, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h529 | h529
                                  · rcases p489_3 (m.d 0 2) (by simp) with h530 | h530
                                    · rcases p489_3 (m.d 0 3) (by simp) with h531 | h531
                                      · linarith only [h4, h531, hlam]
                                      · rcases p489_3 (m.d 0 4) (by simp) with h533 | h533
                                        · linarith only [h5, h533, hlam]
                                        · rcases p489_3 (m.d 0 5) (by simp) with h535 | h535
                                          · linarith only [h535, h6, hlam]
                                          · rcases h3bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h315, h7, hc23, hc34, hlam, hphi, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h330, h7, hc23, hc45, hlam, hphi, ht34, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h7, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h114, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h1, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p537_1, u0elo0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h318, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h320, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h4, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h315, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h324, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h326, hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h330, hc03, hc45, hlam, hphi, ht34, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h315, h330, hc23, hc45, hlam, hphi, ht34, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h330, hc23, hc45, hlam, hphi, ht34, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [hlam, p537_0]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h330, hlam, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              rcases p537_3 (m.d 0 3) (by simp) with h558 | h558
                                              · linarith only [h558, hlam, p537_0]
                                              · rcases p537_3 (m.d 1 3) (by simp) with h560 | h560
                                                · linarith only [h320, h560, hlam]
                                                · rcases p537_3 (m.d 2 3) (by simp) with h562 | h562
                                                  · linarith only [h326, h562, hlam]
                                                  · rcases p537_3 (m.d 3 4) (by simp) with h564 | h564
                                                    · linarith only [h330, h564, hlam]
                                                    · linarith only [h564, h7, hlam]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              rcases p537_3 (m.d 0 3) (by simp) with h567 | h567
                                              · linarith only [h114, h567, hlam]
                                              · linarith only [h1, h567, hlam]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              rcases p537_3 (m.d 0 3) (by simp) with h570 | h570
                                              · linarith only [h114, h570, hlam]
                                              · linarith only [h4, h570, hlam]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [h1, h315, h330, h7, hc23, hc45, hlam, hphi, ht34, p537_1]
                                            · have p537_0 := h537c.1
                                              have p537_1 := h537c.2.1
                                              have p537_2 := h537c.2.2.1
                                              have p537_3 := h537c.2.2.2
                                              linarith only [hlam, p537_0]
                                    · linarith only [h530, h6, hlam]
                                  · linarith only [h3, h529, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h1, hlam, p489_1]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h4, hlam, p489_1]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h7, hlam, p489_1]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h114, hlam, p489_1]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h2, hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h5, hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h1, h134, h315, hc23, hc45, hlam, hphi, ht34, p489_1]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h134, hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h3, hlam, p489_0]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [h6, hlam, p489_1]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h589 | h589
                                  · rcases p489_3 (m.d 0 2) (by simp) with h590 | h590
                                    · rcases p489_3 (m.d 0 3) (by simp) with h591 | h591
                                      · linarith only [h114, h591, hlam]
                                      · rcases p489_3 (m.d 0 4) (by simp) with h593 | h593
                                        · linarith only [h134, h593, hlam]
                                        · linarith only [h593, h7, hlam]
                                    · linarith only [h4, h590, hlam]
                                  · linarith only [h1, h589, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  rcases p489_3 (m.d 0 1) (by simp) with h598 | h598
                                  · rcases p489_3 (m.d 0 2) (by simp) with h599 | h599
                                    · rcases p489_3 (m.d 0 3) (by simp) with h600 | h600
                                      · linarith only [h114, h600, hlam]
                                      · rcases p489_3 (m.d 0 4) (by simp) with h602 | h602
                                        · linarith only [h134, h602, hlam]
                                        · rcases p489_3 (m.d 0 5) (by simp) with h604 | h604
                                          · rcases h3bigk with h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h315, h330, h7, hc23, hc45, hlam, hphi, ht34, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h330, h7, hc23, hc45, hlam, hphi, ht34, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h7, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h114, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h1, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p605_1, u0elo0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h318, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h320, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h4, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h315, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h324, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h326, hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h330, hc03, hc45, hlam, hphi, ht34, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h315, h330, hc23, hc45, hlam, hphi, ht34, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h330, hc23, hc45, hlam, hphi, ht34, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [hlam, p605_0]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h330, hlam, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              rcases p605_3 (m.d 0 3) (by simp) with h626 | h626
                                              · linarith only [h626, hlam, p605_0]
                                              · rcases p605_3 (m.d 1 3) (by simp) with h628 | h628
                                                · linarith only [h320, h628, hlam]
                                                · rcases p605_3 (m.d 2 3) (by simp) with h630 | h630
                                                  · linarith only [h326, h630, hlam]
                                                  · rcases p605_3 (m.d 3 4) (by simp) with h632 | h632
                                                    · linarith only [h330, h632, hlam]
                                                    · linarith only [h632, h7, hlam]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              rcases p605_3 (m.d 0 3) (by simp) with h635 | h635
                                              · linarith only [h114, h635, hlam]
                                              · linarith only [h1, h635, hlam]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              rcases p605_3 (m.d 0 3) (by simp) with h638 | h638
                                              · linarith only [h114, h638, hlam]
                                              · linarith only [h4, h638, hlam]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [h1, h315, h330, h7, hc23, hc45, hlam, hphi, ht34, p605_1]
                                            · have p605_0 := h605c.1
                                              have p605_1 := h605c.2.1
                                              have p605_2 := h605c.2.2.1
                                              have p605_3 := h605c.2.2.2
                                              linarith only [hlam, p605_0]
                                          · linarith only [h134, h604, hlam]
                                    · linarith only [h5, h599, hlam]
                                  · linarith only [h2, h598, hlam]
                                · have p489_0 := h489c.1
                                  have p489_1 := h489c.2.1
                                  have p489_2 := h489c.2.2.1
                                  have p489_3 := h489c.2.2.2
                                  linarith only [hlam, p489_0]
                · linarith only [h317, h6, hc12, hlam, hphi, u2elo0]
              · linarith only [h315, h316, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h315, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h650 | h650
      · rcases m.htr 0 3 5 (by decide) (by decide) with h651 | h651
        · linarith only [h4, h6, h651, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h653 | h653
          · linarith only [h5, h6, h653, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h655 | h655
            · rcases m.htr 1 2 4 (by decide) (by decide) with h656 | h656
              · rcases m.htr 1 2 5 (by decide) (by decide) with h657 | h657
                · linarith only [h0, h6, h657, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h659 | h659
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h660 | h660
                    · linarith only [h1, h651, h660, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h662 | h662
                      · linarith only [h2, h653, h662, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h664 | h664
                        · linarith only [h0, h6, h655, h664, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h1, h651, h659, h664, hc23, hc35, hlam, hphi]
                  · linarith only [h4, h6, h650, h659, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h5, h6, h656, hc12, hlam, hphi, u2elo4]
            · linarith only [h4, h6, h655, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h670 | h670
        · linarith only [h5, h6, h650, h670, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h672 | h672
          · linarith only [h5, h6, h672, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
            · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
              · rcases m.htr 1 2 5 (by decide) (by decide) with h676 | h676
                · linarith only [h6, h676, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
                  · linarith only [h1, h650, h678, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h680 | h680
                    · linarith only [h0, h1, h6, h650, h670, h674, h680, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h682 | h682
                      · linarith only [h0, h1, h6, h650, h672, h675, h682, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                        · linarith only [h4, h6, h684, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h686 | h686
                          · linarith only [h0, h6, h670, h675, h684, h686, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h688 | h688
                            · linarith only [h0, h6, h672, h675, h688, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h690 | h690
                              · linarith only [h0, h6, h675, h684, h688, h690, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h0, h675, h684, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1, u0elo0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  rcases p692_3 (m.d 0 1) (by simp) with h695 | h695
                                  · rcases p692_3 (m.d 0 2) (by simp) with h696 | h696
                                    · linarith only [h0, h696, hlam]
                                    · linarith only [h4, h696, hlam]
                                  · linarith only [h1, h695, hlam]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  rcases p692_3 (m.d 0 1) (by simp) with h700 | h700
                                  · rcases p692_3 (m.d 0 2) (by simp) with h701 | h701
                                    · linarith only [h0, h701, hlam]
                                    · linarith only [h5, h701, hlam]
                                  · linarith only [h2, h700, hlam]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h0, h6, h675, h684, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1, u0elo0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h0, hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h1, h6, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p692_1, u2elo4]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h1, h6, h650, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p692_1, u2elo4]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h6, hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h1, hlam, p692_1]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h4, hlam, p692_1]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h650, hlam, p692_1]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h670, hlam, p692_1]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h2, hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h5, hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h1, h5, h6, h674, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p692_1, u2elo4]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h672, hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h3, hlam, p692_0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [h3, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1, u0elo0]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  rcases p692_3 (m.d 0 1) (by simp) with h723 | h723
                                  · rcases p692_3 (m.d 0 2) (by simp) with h724 | h724
                                    · linarith only [h6, h724, hlam]
                                    · linarith only [h4, h724, hlam]
                                  · linarith only [h1, h723, hlam]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  rcases p692_3 (m.d 0 1) (by simp) with h728 | h728
                                  · rcases p692_3 (m.d 0 2) (by simp) with h729 | h729
                                    · linarith only [h6, h729, hlam]
                                    · linarith only [h5, h729, hlam]
                                  · linarith only [h2, h728, hlam]
                                · have p692_0 := h692c.1
                                  have p692_1 := h692c.2.1
                                  have p692_2 := h692c.2.2.1
                                  have p692_3 := h692c.2.2.2
                                  linarith only [hlam, p692_0]
              · linarith only [h5, h675, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h6, h674, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h736 | h736
    · rcases m.htr 0 3 4 (by decide) (by decide) with h737 | h737
      · linarith only [h4, h5, h737, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h739 | h739
        · rcases m.htr 0 4 5 (by decide) (by decide) with h740 | h740
          · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
            · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
              · linarith only [h5, h742, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h744 | h744
                · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                  · linarith only [h1, h737, h739, h745, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h748 | h748
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h749 | h749
                        · linarith only [h0, h1, h737, h741, h747, h749, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h751 | h751
                          · linarith only [h0, h5, h741, h751, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                          · linarith only [h1, h747, h751, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h5, h740, h742, h748, hc12, hlam, hphi, u2elo3]
                    · linarith only [h4, h5, h739, h747, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h5, h736, h741, h744, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h5, h741, hc12, hlam, hphi, u2elo3]
          · linarith only [h4, h5, h739, h740, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
          · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
            · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
              · linarith only [h5, h761, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h763 | h763
                · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
                  · linarith only [h1, h737, h764, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h766 | h766
                    · linarith only [h1, h739, h766, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h768 | h768
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h769 | h769
                        · linarith only [h0, h5, h737, h760, h769, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                          · linarith only [h1, h739, h760, h771, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h773 | h773
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h774 | h774
                              · rcases h0bigk with h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h0, h763, h771, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p775_1, u0elo0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  rcases p775_3 (m.d 0 1) (by simp) with h778 | h778
                                  · rcases p775_3 (m.d 0 2) (by simp) with h779 | h779
                                    · linarith only [h0, h779, hlam]
                                    · linarith only [h4, h779, hlam]
                                  · linarith only [h1, h778, hlam]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h0, h5, h763, h771, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p775_1, u0elo0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  rcases p775_3 (m.d 0 1) (by simp) with h784 | h784
                                  · rcases p775_3 (m.d 0 2) (by simp) with h785 | h785
                                    · linarith only [h0, h785, hlam]
                                    · linarith only [h736, h785, hlam]
                                  · linarith only [h3, h784, hlam]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h0, hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h1, h5, h760, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p775_1, u2elo3]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h5, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p775_1, u2elo3]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h1, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h4, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h737, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h739, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h2, hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h0, h763, h771, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p775_1, u0elo3]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  rcases p775_3 (m.d 0 1) (by simp) with h801 | h801
                                  · rcases p775_3 (m.d 0 2) (by simp) with h802 | h802
                                    · linarith only [h5, h802, hlam]
                                    · linarith only [h4, h802, hlam]
                                  · linarith only [h1, h801, hlam]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  rcases p775_3 (m.d 0 1) (by simp) with h807 | h807
                                  · rcases p775_3 (m.d 0 2) (by simp) with h808 | h808
                                    · linarith only [h5, h808, hlam]
                                    · linarith only [h736, h808, hlam]
                                  · linarith only [h3, h807, hlam]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h3, hlam, p775_0]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h736, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h1, h5, h736, h760, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p775_1, u2elo3]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [h759, hlam, p775_1]
                                · have p775_0 := h775c.1
                                  have p775_1 := h775c.2.1
                                  have p775_2 := h775c.2.2.1
                                  have p775_3 := h775c.2.2.2
                                  linarith only [hlam, p775_0]
                              · linarith only [h5, h769, h773, h774, hc02, hlam, hphi, u2elo4]
                            · linarith only [h0, h5, h763, h771, h773, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h5, h736, h759, h761, h768, hc12, hlam, hphi, u2elo3]
                · linarith only [h5, h736, h760, h763, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h5, h760, hc12, hlam, hphi, u2elo3]
          · linarith only [h5, h736, h759, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h823 | h823
      · linarith only [h4, h5, h823, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h825 | h825
        · linarith only [h4, h736, h825, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h827 | h827
          · rcases m.htr 1 2 3 (by decide) (by decide) with h828 | h828
            · rcases m.htr 1 2 4 (by decide) (by decide) with h829 | h829
              · linarith only [h0, h5, h829, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h831 | h831
                · linarith only [h0, h736, h831, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
                  · linarith only [h1, h823, h833, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h835 | h835
                    · linarith only [h0, h1, h736, h825, h828, h835, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h837 | h837
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h838 | h838
                        · linarith only [h0, h823, h828, h838, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h840 | h840
                          · linarith only [h3, h4, h5, h825, h831, h840, hc12, hlam, hphi, u2elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                              · rcases h0bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h828, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 1) (by simp) with h847 | h847
                                  · rcases p844_3 (m.d 0 2) (by simp) with h848 | h848
                                    · linarith only [h0, h848, hlam]
                                    · linarith only [h4, h848, hlam]
                                  · linarith only [h1, h847, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h2, h828, h831, h837, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h736, h828, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h1, h736, h828, h842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u2elo3]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h5, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h736, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h1, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h4, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h823, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h825, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h2, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h828, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo3]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 1) (by simp) with h866 | h866
                                  · rcases p844_3 (m.d 0 2) (by simp) with h867 | h867
                                    · linarith only [h5, h867, hlam]
                                    · linarith only [h4, h867, hlam]
                                  · linarith only [h1, h866, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h5, h736, h828, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p844_1, u2elo3]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h3, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h828, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p844_1, u0elo4]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 1) (by simp) with h875 | h875
                                  · rcases p844_3 (m.d 0 2) (by simp) with h876 | h876
                                    · linarith only [h736, h876, hlam]
                                    · linarith only [h4, h876, hlam]
                                  · linarith only [h1, h875, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h827, hlam, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                              · linarith only [h0, h5, h828, h838, h843, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h5, h828, h837, h842, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h5, h827, h828, h829, h837, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h4, h736, h828, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
            · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
              · linarith only [h5, h887, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h889 | h889
                · linarith only [h0, h736, h889, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
                  · linarith only [h1, h2, h823, h886, h887, h891, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h893 | h893
                    · linarith only [h1, h825, h893, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h895 | h895
                      · linarith only [h2, h827, h895, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h897 | h897
                        · linarith only [h0, h5, h823, h886, h897, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h899 | h899
                          · linarith only [h4, h5, h825, h827, h899, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h901 | h901
                            · linarith only [h5, h827, h901, hc02, hlam, hphi, u2elo3]
                            · linarith only [h0, h5, h886, h901, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h886, hc12, hlam, hphi, u2elo3]

end R2N4
