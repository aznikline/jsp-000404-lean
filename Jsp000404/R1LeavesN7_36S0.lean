import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h10, h4, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h8, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
              · linarith only [h0, h14, h2, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
                · linarith only [h0, h16, h2, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h1, h19, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h0, h18, h19, h2, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h18, h2, h22, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h18, h2, h24, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h24, h5, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                · linarith only [h0, h29, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h28, h29, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h27, h28, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
              · linarith only [h0, h2, h27, h33, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                · linarith only [h0, h2, h27, h35, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h1, h38, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h0, h2, h37, h38, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h1, h41, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                      · linarith only [h0, h2, h37, h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h27, h43, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
          · linarith only [h46, h5, h6, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h50, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h4, h49, h50, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h48, h49, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
              · linarith only [h0, h2, h48, h54, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                · linarith only [h3, h5, h54, h56, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h1, h59, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                        · linarith only [h0, h2, h6, h62, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                          · linarith only [h3, h46, h64, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                            · linarith only [h3, h46, h54, h58, h66, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h2bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                rcases p68_3 (m.d 0 2) (by simp) with h70 | h70
                                · rcases p68_3 (m.d 1 2) (by simp) with h71 | h71
                                  · linarith only [h0, h71, hlam]
                                  · rcases p68_3 (m.d 2 3) (by simp) with h73 | h73
                                    · linarith only [h2, h73, hlam]
                                    · linarith only [h48, h73, hlam]
                                · linarith only [h0, h70, hlam]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h48, h58, hc34, hlam, hphi, ht0b, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h56, hlam, hphi, ht0b, ht5b, p68_1, u0elo0, u5ehi1]
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
                                linarith only [h48, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h54, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h56, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h2, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h2, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u0elo2]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h62, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h3, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h61, hlam, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h64, hlam, p68_1]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h4, hlam, p68_0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [h0, h4, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u0elo0]
                              · have p68_0 := h68c.1
                                have p68_1 := h68c.2.1
                                have p68_2 := h68c.2.2.1
                                have p68_3 := h68c.2.2.2
                                linarith only [hlam, p68_0]
                      · linarith only [h1, h58, h61, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h5, h58, h6, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h102 | h102
        · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
          · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
            · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
              · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
                · linarith only [h0, h106, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h104, h106, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h104, h105, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
              · linarith only [h0, h104, h110, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                · linarith only [h0, h104, h112, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                  · linarith only [h102, h114, h5, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                    · linarith only [h0, h110, h114, h116, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · linarith only [h102, h116, h5, hc13, hc34, hlam, hphi]
          · linarith only [h102, h103, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                · linarith only [h0, h123, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h122, h123, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h121, h122, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h127 | h127
              · linarith only [h0, h121, h127, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                · linarith only [h0, h121, h129, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                  · linarith only [h1, h131, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
                    · linarith only [h102, h121, h133, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                      · linarith only [h135, h2, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                        · linarith only [h102, h137, h2, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h0, h139, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                          · linarith only [h120, h127, h139, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 2 5 (by decide) (by decide) with h144 | h144
                · linarith only [h0, h144, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h0, h142, h144, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h142, h143, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
              · linarith only [h0, h142, h148, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                · linarith only [h0, h142, h150, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                  · linarith only [h0, h142, h152, h2, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                    · linarith only [h1, h102, h142, h154, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                      · linarith only [h156, h2, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h102, h158, h2, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                          · linarith only [h120, h160, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                            · linarith only [h120, h142, h162, h2, h5, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h142, h162, h2, h5, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h165 | h165
      · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
        · linarith only [h166, h2, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
          · linarith only [h165, h168, h2, h4, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
            · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
              · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                · linarith only [h0, h172, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                    · linarith only [h1, h166, h175, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                      · linarith only [h0, h170, h177, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h166, h174, h177, hc23, hc35, hlam, hphi]
                  · linarith only [h165, h166, h174, hc13, hc35, hlam, hphi]
              · linarith only [h171, h3, h4, hc12, hc25, hlam, hphi]
            · linarith only [h170, h2, h4, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
        · linarith only [h183, h2, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
          · linarith only [h185, h3, h4, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
            · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
              · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                · linarith only [h0, h189, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                  · linarith only [h1, h165, h191, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                    · linarith only [h0, h183, h188, h191, h193, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                      · linarith only [h1, h165, h187, h195, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                        · linarith only [h1, h183, h187, h197, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                          · linarith only [h0, h165, h185, h188, h199, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                            · linarith only [h199, h2, h201, h4, hc23, hc34, hlam, hphi]
                            · rcases h2bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h188, h195, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p203_1, u0elo1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h197, h4, hc23, hc35, hlam, hphi, p203_1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h195, h197, h4, hc23, hc35, hlam, hphi, p203_1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h4, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h0, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p203_1, u0elo0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h0, h195, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p203_1, u0elo0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h189, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h2, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h187, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h195, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h197, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h3, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h188, hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h197, h3, h4, hc23, hc35, hlam, hphi, p203_1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [hlam, p203_0]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h199, hlam, p203_1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h197, h2, hc23, hc35, hlam, hphi, p203_1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [h187, h197, hc23, hc35, hlam, hphi, p203_1]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                rcases p203_3 (m.d 0 2) (by simp) with h226 | h226
                                · linarith only [h226, h4, hlam]
                                · linarith only [h2, h226, hlam]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                rcases p203_3 (m.d 0 2) (by simp) with h229 | h229
                                · linarith only [h229, h4, hlam]
                                · linarith only [h229, h3, hlam]
                              · have p203_0 := h203c.1
                                have p203_1 := h203c.2.1
                                have p203_2 := h203c.2.2.1
                                have p203_3 := h203c.2.2.2
                                linarith only [hlam, p203_0]
              · linarith only [h188, h3, h4, hc12, hc25, hlam, hphi]
            · linarith only [h187, h2, h4, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h235 | h235
    · rcases m.htr 0 3 4 (by decide) (by decide) with h236 | h236
      · linarith only [h2, h236, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h238 | h238
        · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
          · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
            · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
              · linarith only [h0, h2, h238, h241, h3, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
                · linarith only [h0, h243, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h235, h240, h243, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h2, h240, h3, hc12, hc24, hlam, hphi]
          · linarith only [h2, h238, h239, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h248 | h248
          · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
            · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
              · linarith only [h0, h250, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                · linarith only [h0, h252, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                · linarith only [h235, h252, h3, hc12, hc24, hlam, hphi]
            · linarith only [h2, h249, h3, hc12, hc24, hlam, hphi]
          · linarith only [h235, h248, h3, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h257 | h257
      · linarith only [h2, h257, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h259 | h259
        · linarith only [h2, h235, h259, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
          · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
            · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
              · linarith only [h0, h263, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                · linarith only [h0, h235, h265, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h267 | h267
                  · linarith only [h1, h2, h257, h267, h3, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h269 | h269
                    · linarith only [h1, h259, h269, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h271 | h271
                      · linarith only [h0, h257, h262, h271, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                        · linarith only [h1, h259, h262, h273, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h276 | h276
                            · rcases h2bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h262, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p277_1, u0elo1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h235, h271, h275, hc23, hc34, hlam, hphi, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h3, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h235, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h0, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p277_1, u0elo0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h263, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h265, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h2, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h262, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h271, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h273, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h2, h271, hc23, hc34, hlam, hphi, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h262, h271, hc23, hc34, hlam, hphi, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                rcases p277_3 (m.d 0 2) (by simp) with h295 | h295
                                · linarith only [h295, h3, hlam]
                                · linarith only [h2, h295, hlam]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h0, h235, h262, h271, hc23, hc34, hlam, hphi, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h0, h262, h273, hc23, hc35, hlam, hphi, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h262, h273, hc23, hc35, hlam, hphi, p277_1]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                rcases p277_3 (m.d 0 2) (by simp) with h302 | h302
                                · linarith only [h235, h302, hlam]
                                · linarith only [h2, h302, hlam]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [h275, hlam, p277_0]
                              · have p277_0 := h277c.1
                                have p277_1 := h277c.2.1
                                have p277_2 := h277c.2.2.1
                                have p277_3 := h277c.2.2.2
                                linarith only [hlam, p277_0]
                            · linarith only [h261, h265, h271, h275, h276, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi1]
                          · linarith only [h261, h275, h3, hlam]
            · linarith only [h2, h262, h3, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
            · rcases m.htr 1 2 4 (by decide) (by decide) with h311 | h311
              · linarith only [h0, h3, h311, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h313 | h313
                · linarith only [h0, h235, h313, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h315 | h315
                  · linarith only [h1, h2, h257, h3, h315, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h317 | h317
                    · linarith only [h1, h259, h317, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                      · linarith only [h0, h257, h310, h319, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                        · linarith only [h1, h259, h310, h321, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
                          · linarith only [h0, h261, h3, h310, h319, h323, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h3, h310, h323, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2, h3, h310, hc12, hc24, hlam, hphi]

end R2N4
