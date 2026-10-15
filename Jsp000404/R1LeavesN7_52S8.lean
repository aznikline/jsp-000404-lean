import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h10, h13, h3, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h0, h12, h13, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h12, h16, h4, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h18, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h12, h18, h20, h4, h5, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                            · linarith only [h0, h10, h18, h20, h22, h4, h5, h7, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                            · linarith only [h0, h10, h20, h22, h4, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h25, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                    · linarith only [h27, h8, h9, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h27, h29, h4, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h27, h31, h4, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · linarith only [h0, h31, h4, h5, h7, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h34, h4, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                  · linarith only [h0, h36, h4, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h1, h39, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h0, h38, h39, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h1, h42, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h0, h38, h4, h44, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h38, h4, h46, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h0, h4, h46, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                  · linarith only [h0, h51, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h1, h54, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h0, h4, h53, h54, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h1, h57, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                        · linarith only [h0, h4, h50, h51, h57, h59, h6, h7, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                          · linarith only [h0, h4, h49, h51, h53, h57, h6, h61, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                            · linarith only [h1, h49, h57, h63, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
                            · linarith only [h0, h4, h50, h51, h6, h61, h63, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h0, h66, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                    · linarith only [h49, h50, h68, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
                      · linarith only [h0, h4, h5, h68, h70, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
                        · linarith only [h0, h4, h5, h68, h7, h72, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                          · linarith only [h0, h4, h68, h74, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h0, h4, h49, h5, h50, h74, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h4, h49, h77, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h4, h49, h79, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                      · linarith only [h0, h4, h49, h82, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h0, h4, h6, h81, h82, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h4, h5, h81, h85, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h49, h5, h7, h81, h87, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                          · linarith only [h0, h4, h49, h81, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h1, h49, h5, h89, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
            · linarith only [h5, h6, h92, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
              · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                  · linarith only [h0, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                      · linarith only [h1, h6, h99, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                        · linarith only [h101, h2, h92, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                          · linarith only [h0, h103, h94, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h1, h103, h6, h98, hc23, hc35, hlam, hphi]
                    · linarith only [h5, h6, h98, hc13, hc35, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                  · linarith only [h0, h107, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                    · linarith only [h109, h94, h95, hlam]
                    · linarith only [h109, h5, h6, hc13, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                · linarith only [h0, h112, h4, h94, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h0, h114, h4, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                      · linarith only [h1, h117, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h0, h116, h119, h4, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                            · linarith only [h122, h4, h6, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                              · linarith only [h0, h121, h124, h4, h92, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                                · linarith only [h116, h124, h126, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases h3bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h116, h6, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h126, h6, hc23, hc45, hlam, hphi, ht34, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h126, h6, hc34, hc45, hlam, hphi, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h6, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h1, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h94, hlam, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p128_1, u1elo0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h117, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h4, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h0, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p128_1, u1elo0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h0, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p128_1, u1elo0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h122, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h5, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h116, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h121, hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [hlam, p128_0]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h126, hlam, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h1, h116, h126, hc34, hc45, hlam, hphi, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h116, h126, hc34, hc45, hlam, hphi, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [h112, h121, h126, hc12, hc45, hlam, hphi, ht23, ht34, p128_1]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    rcases p128_3 (m.d 0 3) (by simp) with h152 | h152
                                    · linarith only [h152, h6, hlam]
                                    · linarith only [h152, h5, hlam]
                                  · have p128_0 := h128c.1
                                    have p128_1 := h128c.2.1
                                    have p128_2 := h128c.2.2.1
                                    have p128_3 := h128c.2.2.2
                                    linarith only [hlam, p128_0]
                          · linarith only [h1, h116, h121, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h116, h5, h6, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h158 | h158
          · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
              · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
                · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h0, h162, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h164 | h164
                    · linarith only [h158, h164, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h1, h166, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h158, h166, h5, hc13, hc34, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                  · linarith only [h0, h169, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                    · linarith only [h158, h171, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h160, h161, h173, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h158, h173, h5, hc13, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
                · linarith only [h0, h160, h176, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                  · linarith only [h0, h160, h178, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                    · linarith only [h158, h180, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                      · linarith only [h0, h160, h182, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h158, h182, h5, hc13, hc34, hlam, hphi]
            · linarith only [h158, h159, h5, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
            · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
              · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                  · linarith only [h0, h189, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h191 | h191
                    · linarith only [h1, h191, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                      · linarith only [h1, h158, h193, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                        · linarith only [h188, h189, h195, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                          · linarith only [h0, h197, h4, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                            · linarith only [h1, h158, h187, h199, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                              · linarith only [h188, h189, h195, h201, hlam]
                              · linarith only [h186, h188, h189, h197, h201, h5, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                  · linarith only [h0, h204, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                    · linarith only [h186, h206, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                      · linarith only [h187, h188, h2, h208, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h210 | h210
                        · linarith only [h2, h210, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · linarith only [h186, h187, h188, h2, h210, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                · linarith only [h0, h187, h213, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h0, h187, h215, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
                    · linarith only [h1, h217, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h219 | h219
                      · linarith only [h1, h158, h219, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                        · linarith only [h2, h221, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                          · linarith only [h0, h186, h187, h217, h221, h223, h4, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                            · linarith only [h158, h225, h4, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                                · rcases h3bigk with h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c | h229c
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h158, h187, h228, hc12, hc34, hlam, hphi, ht23, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h158, h228, hc23, hc34, hlam, hphi, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h5, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h158, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h1, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h187, hlam, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h217, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h219, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h4, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h0, h187, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p229_1, u1elo0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h223, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h225, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h187, h4, hc12, hc34, hlam, hphi, ht23, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    rcases p229_3 (m.d 0 3) (by simp) with h246 | h246
                                    · linarith only [h246, h5, hlam]
                                    · linarith only [h1, h246, hlam]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h187, hc12, hc34, hlam, hphi, ht23, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h158, h187, h4, hc12, hc34, hlam, hphi, ht23, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h187, h4, hc12, hc35, hlam, hphi, ht23, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    rcases p229_3 (m.d 0 3) (by simp) with h253 | h253
                                    · linarith only [h158, h253, hlam]
                                    · linarith only [h1, h253, hlam]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h187, h228, hc12, hc34, hlam, hphi, ht23, p229_1]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [h228, hlam, p229_0]
                                  · have p229_0 := h229c.1
                                    have p229_1 := h229c.2.1
                                    have p229_2 := h229c.2.2.1
                                    have p229_3 := h229c.2.2.2
                                    linarith only [hlam, p229_0]
                                · linarith only [h186, h187, h228, h4, h5, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h186, h2, h213, h227, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
              · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                  · linarith only [h0, h263, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h265 | h265
                    · linarith only [h1, h265, h5, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                      · linarith only [h1, h267, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                        · linarith only [h262, h263, h269, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h271 | h271
                          · linarith only [h261, h263, h271, h3, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                            · linarith only [h1, h158, h261, h273, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
                              · linarith only [h186, h262, h263, h275, h3, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                                · linarith only [h261, h263, h275, h277, hc23, hc34, hlam, hphi]
                                · rcases h3bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h261, h277, h5, hc23, hc45, hlam, hphi, ht34, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h277, h5, hc23, hc45, hlam, hphi, ht34, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h5, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h158, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h1, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p279_1, u1elo0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h265, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h267, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h4, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h261, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h271, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h273, hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h277, hc03, hc45, hlam, hphi, ht34, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h261, h277, hc23, hc45, hlam, hphi, ht34, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h277, hc23, hc45, hlam, hphi, ht34, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [hlam, p279_0]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h277, hlam, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    rcases p279_3 (m.d 0 3) (by simp) with h300 | h300
                                    · linarith only [h300, hlam, p279_0]
                                    · rcases p279_3 (m.d 1 3) (by simp) with h302 | h302
                                      · linarith only [h267, h302, hlam]
                                      · rcases p279_3 (m.d 2 3) (by simp) with h304 | h304
                                        · linarith only [h273, h304, hlam]
                                        · rcases p279_3 (m.d 3 4) (by simp) with h306 | h306
                                          · linarith only [h277, h306, hlam]
                                          · linarith only [h306, h5, hlam]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    rcases p279_3 (m.d 0 3) (by simp) with h309 | h309
                                    · linarith only [h158, h309, hlam]
                                    · linarith only [h1, h309, hlam]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    rcases p279_3 (m.d 0 3) (by simp) with h312 | h312
                                    · linarith only [h158, h312, hlam]
                                    · linarith only [h312, h4, hlam]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [h1, h261, h5, hc23, hc35, hlam, hphi, p279_1]
                                  · have p279_0 := h279c.1
                                    have p279_1 := h279c.2.1
                                    have p279_2 := h279c.2.2.1
                                    have p279_3 := h279c.2.2.2
                                    linarith only [hlam, p279_0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                  · linarith only [h0, h317, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                    · linarith only [h1, h319, h5, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
                      · linarith only [h2, h261, h262, h321, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                        · linarith only [h2, h323, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                          · linarith only [h0, h325, h4, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                            · linarith only [h1, h158, h261, h327, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h329 | h329
                              · linarith only [h186, h2, h261, h262, h325, h329, hc23, hc34, hlam, hphi]
                              · linarith only [h261, h262, h329, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h332 | h332
                · linarith only [h0, h261, h332, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                  · linarith only [h0, h334, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                    · linarith only [h0, h261, h336, h4, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h338 | h338
                      · linarith only [h158, h261, h338, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h340 | h340
                        · linarith only [h186, h2, h340, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                          · linarith only [h342, h4, h5, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h344 | h344
                            · linarith only [h158, h344, h4, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h346 | h346
                              · linarith only [h186, h261, h346, h4, h5, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                                · linarith only [h186, h261, h348, h4, h5, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h261, h348, h4, h5, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h351 | h351
        · rcases m.htr 0 3 5 (by decide) (by decide) with h352 | h352
          · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
            · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
              · linarith only [h0, h354, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                  · linarith only [h0, h357, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                      · linarith only [h1, h360, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h1, h352, h359, h360, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h351, h354, h356, h359, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                  · linarith only [h0, h364, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h366 | h366
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                      · linarith only [h1, h367, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h1, h352, h366, h367, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h370 | h370
                      · linarith only [h1, h370, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h372 | h372
                        · linarith only [h1, h351, h366, h372, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h374 | h374
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h376 | h376
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h377 | h377
                                · linarith only [h1, h351, h354, h366, h372, h377, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h354, h366, h376, h377, hc12, hc24, hlam, hphi]
                              · linarith only [h1, h351, h353, h356, h376, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h352, h375, h4, hlam]
                          · linarith only [h351, h374, h4, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
              · linarith only [h352, h383, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h1, h383, h386, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h389 | h389
                      · linarith only [h1, h389, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h1, h352, h383, h385, h389, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h351, h383, h385, h388, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                  · linarith only [h0, h393, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h395 | h395
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h396 | h396
                      · linarith only [h1, h396, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h1, h352, h395, h396, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                      · linarith only [h1, h399, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                        · linarith only [h1, h351, h353, h395, h401, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h405 | h405
                              · linarith only [h351, h353, h383, h395, h405, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h407 | h407
                                · linarith only [h1, h351, h405, h407, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases h3bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    rcases p409_3 (m.d 0 3) (by simp) with h411 | h411
                                    · rcases p409_3 (m.d 1 3) (by simp) with h412 | h412
                                      · linarith only [h1, h412, hlam]
                                      · rcases p409_3 (m.d 2 3) (by simp) with h414 | h414
                                        · rcases p409_3 (m.d 3 4) (by simp) with h415 | h415
                                          · linarith only [h351, h415, hlam]
                                          · linarith only [h395, h415, hlam]
                                        · linarith only [h383, h414, hlam]
                                    · linarith only [h1, h411, hlam]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h4, hlam, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h1, h383, h395, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u1elo0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, p409_1, u1elo0, u5ehi3]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h1, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h383, hlam, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h395, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h399, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h351, h383, h395, hc12, hc23, hlam, hphi, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    rcases p409_3 (m.d 0 3) (by simp) with h429 | h429
                                    · linarith only [h4, h429, hlam]
                                    · linarith only [h1, h429, hlam]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h383, h395, hc12, hc23, hlam, hphi, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h383, h395, h407, hc12, hc23, hlam, hphi, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h351, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h351, h353, h383, hc12, hc45, hlam, hphi, ht23, ht34, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h403, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h407, hlam, p409_1]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h352, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h1, h352, h383, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p409_1, u1elo0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h404, hlam, p409_0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [h1, h352, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p409_1, u1elo0]
                                  · have p409_0 := h409c.1
                                    have p409_1 := h409c.2.1
                                    have p409_2 := h409c.2.2.1
                                    have p409_3 := h409c.2.2.2
                                    linarith only [hlam, p409_0]
                            · linarith only [h0, h1, h352, h4, h404, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h351, h4, h403, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h447 | h447
            · linarith only [h351, h352, h447, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h449 | h449
              · linarith only [h0, h351, h4, h449, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
                  · linarith only [h0, h452, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h455 | h455
                      · linarith only [h1, h352, h4, h455, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h457 | h457
                        · linarith only [h0, h447, h451, h457, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h459 | h459
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h460 | h460
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h461 | h461
                              · linarith only [h2, h447, h451, h461, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h463 | h463
                                · linarith only [h1, h352, h449, h451, h459, h460, h461, h463, hlam]
                                · rcases h3bigk with h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c | h465c
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h352, h449, h451, h459, h460, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h4, hlam, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h352, h460, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h352, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h1, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h449, hlam, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p465_1, u1elo0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h455, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    rcases p465_3 (m.d 0 3) (by simp) with h476 | h476
                                    · linarith only [h4, h476, hlam]
                                    · rcases p465_3 (m.d 1 3) (by simp) with h478 | h478
                                      · linarith only [h449, h478, hlam]
                                      · rcases p465_3 (m.d 2 3) (by simp) with h480 | h480
                                        · rcases p465_3 (m.d 3 4) (by simp) with h481 | h481
                                          · linarith only [h459, h481, hlam]
                                          · rcases p465_3 (m.d 3 5) (by simp) with h483 | h483
                                            · linarith only [h460, h483, hlam]
                                            · linarith only [h352, h483, hlam]
                                        · linarith only [h4, h480, hlam]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    rcases p465_3 (m.d 0 3) (by simp) with h487 | h487
                                    · linarith only [h4, h487, hlam]
                                    · linarith only [h1, h487, hlam]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h0, h352, h4, h451, h459, h460, hlam, p465_2]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h352, h4, hc02, hc23, hlam, hphi, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h351, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h454, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h459, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h463, hlam, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h0, h4, h451, h459, h460, h461, hc34, hc45, hlam, hphi, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h449, h451, h459, h460, h461, hc34, hc45, hlam, hphi, p465_1]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [h460, hlam, p465_0]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    rcases p465_3 (m.d 0 3) (by simp) with h501 | h501
                                    · linarith only [h352, h501, hlam]
                                    · linarith only [h351, h501, hlam]
                                  · have p465_0 := h465c.1
                                    have p465_1 := h465c.2.1
                                    have p465_2 := h465c.2.2.1
                                    have p465_3 := h465c.2.2.2
                                    linarith only [hlam, p465_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h505 | h505
                              · linarith only [h3, h449, h451, h455, h505, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                                · linarith only [h2, h4, h451, h459, h460, h505, h507, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h0, h4, h451, h459, h460, h507, hc34, hc45, hlam, hphi]
                          · linarith only [h351, h4, h459, hlam]
                    · linarith only [h351, h352, h454, hc13, hc35, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h512 | h512
                  · linarith only [h0, h512, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h514 | h514
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h515 | h515
                      · linarith only [h1, h352, h515, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
                        · linarith only [h2, h517, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                                · linarith only [h1, h352, h447, h514, h520, h522, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases h3bigk with h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h352, h519, h521, h522, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h4, hlam, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h352, h519, h521, h522, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h352, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h1, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h449, hlam, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p524_1, u1elo0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h515, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    rcases p524_3 (m.d 0 3) (by simp) with h535 | h535
                                    · linarith only [h4, h535, hlam]
                                    · rcases p524_3 (m.d 1 3) (by simp) with h537 | h537
                                      · linarith only [h449, h537, hlam]
                                      · rcases p524_3 (m.d 2 3) (by simp) with h539 | h539
                                        · rcases p524_3 (m.d 3 4) (by simp) with h540 | h540
                                          · linarith only [h519, h540, hlam]
                                          · rcases p524_3 (m.d 3 5) (by simp) with h542 | h542
                                            · linarith only [h520, h542, hlam]
                                            · linarith only [h352, h542, hlam]
                                        · linarith only [h4, h539, hlam]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    rcases p524_3 (m.d 0 3) (by simp) with h546 | h546
                                    · linarith only [h4, h546, hlam]
                                    · linarith only [h1, h546, hlam]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h351, h352, h519, h521, h522, hlam, p524_2]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h352, h4, hc02, hc23, hlam, hphi, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h351, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h514, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h519, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h522, hlam, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h1, h514, h520, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h514, h520, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p524_1]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [h520, hlam, p524_0]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    rcases p524_3 (m.d 0 3) (by simp) with h560 | h560
                                    · linarith only [h352, h560, hlam]
                                    · linarith only [h351, h560, hlam]
                                  · have p524_0 := h524c.1
                                    have p524_1 := h524c.2.1
                                    have p524_2 := h524c.2.2.1
                                    have p524_3 := h524c.2.2.2
                                    linarith only [hlam, p524_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                                · linarith only [h1, h451, h514, h521, h564, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h3bigk with h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c | h566c
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h352, h514, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h4, hlam, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h352, h520, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h352, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h1, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h449, hlam, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p566_1, u1elo0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h515, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    rcases p566_3 (m.d 0 3) (by simp) with h577 | h577
                                    · linarith only [h4, h577, hlam]
                                    · rcases p566_3 (m.d 1 3) (by simp) with h579 | h579
                                      · linarith only [h449, h579, hlam]
                                      · rcases p566_3 (m.d 2 3) (by simp) with h581 | h581
                                        · rcases p566_3 (m.d 3 4) (by simp) with h582 | h582
                                          · linarith only [h519, h582, hlam]
                                          · rcases p566_3 (m.d 3 5) (by simp) with h584 | h584
                                            · linarith only [h520, h584, hlam]
                                            · linarith only [h352, h584, hlam]
                                        · linarith only [h4, h581, hlam]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    rcases p566_3 (m.d 0 3) (by simp) with h588 | h588
                                    · linarith only [h4, h588, hlam]
                                    · linarith only [h1, h588, hlam]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h351, h352, h520, hlam, p566_2]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h0, h352, h4, hc12, hc23, hlam, hphi, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h351, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h514, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h519, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h564, hlam, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h351, h520, h521, hc34, hc45, hlam, hphi, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h514, h520, h521, hc34, hc45, hlam, hphi, p566_1]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [h520, hlam, p566_0]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    rcases p566_3 (m.d 0 3) (by simp) with h602 | h602
                                    · linarith only [h352, h602, hlam]
                                    · linarith only [h351, h602, hlam]
                                  · have p566_0 := h566c.1
                                    have p566_1 := h566c.2.1
                                    have p566_2 := h566c.2.2.1
                                    have p566_3 := h566c.2.2.2
                                    linarith only [hlam, p566_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
                              · linarith only [h2, h447, h451, h519, h520, h606, hc12, hc35, hlam, hphi, ht23]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h608 | h608
                                · linarith only [h1, h451, h514, h606, h608, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h3bigk with h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h4, h520, h608, hc13, hc45, hlam, hphi, ht34, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h4, hlam, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h4, h520, h608, hc34, hc45, hlam, hphi, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h352, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h1, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h449, hlam, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p610_1, u1elo0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h515, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h520, h608, hc03, hc45, hlam, hphi, ht34, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h520, h608, hc13, hc45, hlam, hphi, ht34, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h520, h608, hc34, hc45, hlam, hphi, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h520, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h351, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h514, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h519, hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [hlam, p610_0]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h608, hlam, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h1, h514, h608, hc34, hc45, hlam, hphi, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h514, h608, hc34, hc45, hlam, hphi, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [h0, h4, h608, hc12, hc45, hlam, hphi, ht23, ht34, p610_1]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    rcases p610_3 (m.d 0 3) (by simp) with h634 | h634
                                    · linarith only [h352, h634, hlam]
                                    · linarith only [h351, h634, hlam]
                                  · have p610_0 := h610c.1
                                    have p610_1 := h610c.2.1
                                    have p610_2 := h610c.2.2.1
                                    have p610_3 := h610c.2.2.2
                                    linarith only [hlam, p610_0]
                          · linarith only [h0, h4, h514, h519, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h351, h352, h514, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h640 | h640
          · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
            · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
              · linarith only [h0, h4, h642, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
                · rcases m.htr 1 2 5 (by decide) (by decide) with h645 | h645
                  · linarith only [h0, h645, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h647 | h647
                    · linarith only [h1, h351, h647, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h642, h644, h647, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
                  · linarith only [h0, h650, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h652 | h652
                    · linarith only [h1, h351, h640, h652, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h654 | h654
                      · linarith only [h2, h652, h654, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · linarith only [h351, h640, h642, h654, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h351, h640, h641, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
            · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
              · linarith only [h0, h4, h659, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
                · rcases m.htr 1 2 5 (by decide) (by decide) with h662 | h662
                  · linarith only [h0, h662, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                    · linarith only [h1, h351, h4, h664, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h659, h661, h664, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h667 | h667
                  · linarith only [h1, h659, h667, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                    · linarith only [h1, h351, h4, h669, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h671 | h671
                      · linarith only [h0, h1, h4, h640, h671, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h673 | h673
                        · linarith only [h2, h673, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h675 | h675
                          · linarith only [h351, h658, h659, h669, h673, h675, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h677 | h677
                            · linarith only [h640, h658, h659, h669, h673, h675, h677, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h679 | h679
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h680 | h680
                                · rcases h3bigk with h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h4, h659, h677, h680, hc12, hc34, hlam, hphi, ht23, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h4, hlam, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h351, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h640, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h1, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h659, hlam, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h669, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h671, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h677, h680, hc03, hc34, hlam, hphi, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h659, h677, h680, hc12, hc34, hlam, hphi, ht23, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h675, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h677, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    rcases p681_3 (m.d 0 3) (by simp) with h697 | h697
                                    · linarith only [h697, hlam, p681_0]
                                    · rcases p681_3 (m.d 1 3) (by simp) with h699 | h699
                                      · linarith only [h669, h699, hlam]
                                      · rcases p681_3 (m.d 2 3) (by simp) with h701 | h701
                                        · linarith only [h675, h701, hlam]
                                        · linarith only [h4, h701, hlam]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    rcases p681_3 (m.d 0 3) (by simp) with h704 | h704
                                    · linarith only [h351, h704, hlam]
                                    · linarith only [h1, h704, hlam]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h1, h640, h659, hc12, hc34, hlam, hphi, ht23, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    rcases p681_3 (m.d 0 3) (by simp) with h710 | h710
                                    · linarith only [h710, hlam, p681_0]
                                    · rcases p681_3 (m.d 1 3) (by simp) with h712 | h712
                                      · linarith only [h671, h712, hlam]
                                      · rcases p681_3 (m.d 2 3) (by simp) with h714 | h714
                                        · linarith only [h677, h714, hlam]
                                        · linarith only [h4, h714, hlam]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    rcases p681_3 (m.d 0 3) (by simp) with h717 | h717
                                    · linarith only [h640, h717, hlam]
                                    · linarith only [h1, h717, hlam]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p681_1]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [h680, hlam, p681_0]
                                  · have p681_0 := h681c.1
                                    have p681_1 := h681c.2.1
                                    have p681_2 := h681c.2.2.1
                                    have p681_3 := h681c.2.2.2
                                    linarith only [hlam, p681_0]
                                · linarith only [h1, h2, h351, h658, h659, h680, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h2, h658, h661, h679, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
              · linarith only [h0, h4, h725, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
                · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
                  · linarith only [h0, h728, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h730 | h730
                    · linarith only [h1, h351, h4, h730, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h725, h727, h730, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                  · linarith only [h0, h733, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                    · linarith only [h1, h351, h4, h735, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h737 | h737
                      · linarith only [h1, h737, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                        · linarith only [h2, h351, h4, h658, h739, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h741 | h741
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h742 | h742
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h743 | h743
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h744 | h744
                                · linarith only [h0, h351, h4, h658, h741, h744, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h351, h4, h743, h744, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                                · linarith only [h0, h351, h4, h658, h741, h747, hc12, hc23, hlam, hphi]
                                · rcases h3bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h351, hc13, hc34, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h4, hlam, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h351, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h640, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h1, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h725, hlam, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h735, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h737, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    rcases p749_3 (m.d 0 3) (by simp) with h760 | h760
                                    · linarith only [h4, h760, hlam]
                                    · rcases p749_3 (m.d 1 3) (by simp) with h762 | h762
                                      · linarith only [h725, h762, hlam]
                                      · rcases p749_3 (m.d 2 3) (by simp) with h764 | h764
                                        · rcases p749_3 (m.d 3 4) (by simp) with h765 | h765
                                          · linarith only [h741, h765, hlam]
                                          · linarith only [h351, h765, hlam]
                                        · linarith only [h4, h764, hlam]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    rcases p749_3 (m.d 0 3) (by simp) with h769 | h769
                                    · linarith only [h4, h769, hlam]
                                    · linarith only [h1, h769, hlam]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h351, h4, hc02, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h0, h4, h640, hc12, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h0, h4, h741, hc12, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h725, h741, hc12, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h741, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h747, hlam, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h0, h4, h742, hc12, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h725, h742, hc12, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h742, hlam, p749_0]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [h0, h351, h4, h742, hc12, hc23, hlam, hphi, p749_1]
                                  · have p749_0 := h749c.1
                                    have p749_1 := h749c.2.1
                                    have p749_2 := h749c.2.2.1
                                    have p749_3 := h749c.2.2.2
                                    linarith only [hlam, p749_0]
                            · linarith only [h0, h351, h4, h741, h742, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h786 | h786
                            · linarith only [h0, h4, h640, h741, h786, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h788 | h788
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
                                · rcases h3bigk with h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h351, h658, h725, h788, hc12, hc24, hlam, hphi, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h4, hlam, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h351, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h640, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h1, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h725, hlam, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h735, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h737, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h786, h789, hc03, hc34, hlam, hphi, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h725, h786, h789, hc12, hc34, hlam, hphi, ht23, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h741, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h786, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    rcases p790_3 (m.d 0 3) (by simp) with h806 | h806
                                    · linarith only [h806, hlam, p790_0]
                                    · rcases p790_3 (m.d 1 3) (by simp) with h808 | h808
                                      · linarith only [h735, h808, hlam]
                                      · rcases p790_3 (m.d 2 3) (by simp) with h810 | h810
                                        · linarith only [h741, h810, hlam]
                                        · linarith only [h4, h810, hlam]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    rcases p790_3 (m.d 0 3) (by simp) with h813 | h813
                                    · linarith only [h351, h813, hlam]
                                    · linarith only [h1, h813, hlam]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h1, h640, h725, hc12, hc34, hlam, hphi, ht23, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    rcases p790_3 (m.d 0 3) (by simp) with h819 | h819
                                    · linarith only [h819, hlam, p790_0]
                                    · rcases p790_3 (m.d 1 3) (by simp) with h821 | h821
                                      · linarith only [h737, h821, hlam]
                                      · rcases p790_3 (m.d 2 3) (by simp) with h823 | h823
                                        · linarith only [h786, h823, hlam]
                                        · linarith only [h4, h823, hlam]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    rcases p790_3 (m.d 0 3) (by simp) with h826 | h826
                                    · linarith only [h640, h826, hlam]
                                    · linarith only [h1, h826, hlam]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p790_1]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [h789, hlam, p790_0]
                                  · have p790_0 := h790c.1
                                    have p790_1 := h790c.2.1
                                    have p790_2 := h790c.2.2.1
                                    have p790_3 := h790c.2.2.2
                                    linarith only [hlam, p790_0]
                                · linarith only [h741, h788, h789, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h833 | h833
                                · linarith only [h0, h4, h741, h788, h833, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h4, h741, h833, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h836 | h836
      · rcases m.htr 0 3 4 (by decide) (by decide) with h837 | h837
        · rcases m.htr 0 3 5 (by decide) (by decide) with h838 | h838
          · linarith only [h1, h3, h838, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h840 | h840
            · linarith only [h0, h3, h836, h837, h840, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
              · linarith only [h0, h3, h842, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
              · linarith only [h0, h3, h836, h842, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h845 | h845
          · linarith only [h0, h3, h836, h845, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h847 | h847
            · linarith only [h2, h3, h847, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
              · linarith only [h0, h3, h849, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
              · linarith only [h0, h3, h836, h849, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h852 | h852
        · rcases m.htr 0 3 5 (by decide) (by decide) with h853 | h853
          · linarith only [h1, h3, h853, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h855 | h855
            · linarith only [h1, h3, h852, h855, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
              · linarith only [h0, h3, h836, h857, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h859 | h859
                · linarith only [h0, h3, h859, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h861 | h861
                  · linarith only [h1, h3, h857, h861, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h863 | h863
                    · linarith only [h1, h3, h863, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · linarith only [h1, h3, h852, h857, h863, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h866 | h866
          · linarith only [h2, h3, h852, h866, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h868 | h868
            · linarith only [h2, h3, h868, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h870 | h870
              · linarith only [h0, h3, h836, h870, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h872 | h872
                · linarith only [h1, h3, h870, h872, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
                  · linarith only [h1, h3, h870, h874, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
                    · linarith only [h1, h3, h836, h852, h876, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                      · linarith only [h1, h3, h866, h878, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h880 | h880
                        · linarith only [h2, h3, h868, h880, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h882 | h882
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h883 | h883
                            · linarith only [h0, h3, h878, h883, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h836, h852, h882, h883, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h886 | h886
                            · linarith only [h0, h836, h866, h882, h886, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h888 | h888
                              · linarith only [h2, h3, h870, h876, h880, h888, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h890 | h890
                                · linarith only [h0, h836, h882, h888, h890, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h836, h882, h890, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h893 | h893
    · linarith only [h2, h893, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h895 | h895
      · rcases m.htr 0 3 4 (by decide) (by decide) with h896 | h896
        · linarith only [h1, h2, h896, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h898 | h898
          · linarith only [h0, h2, h895, h898, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
            · rcases m.htr 1 2 3 (by decide) (by decide) with h901 | h901
              · linarith only [h0, h2, h901, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h0, h2, h895, h901, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h904 | h904
              · linarith only [h0, h2, h904, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · linarith only [h0, h2, h895, h904, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
        · linarith only [h1, h2, h907, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h909 | h909
          · linarith only [h1, h2, h909, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h911 | h911
            · rcases m.htr 1 2 3 (by decide) (by decide) with h912 | h912
              · linarith only [h0, h2, h895, h912, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h914 | h914
                · linarith only [h0, h2, h914, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h916 | h916
                  · linarith only [h1, h2, h912, h916, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h918 | h918
                    · linarith only [h1, h2, h907, h918, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h920 | h920
                      · linarith only [h1, h2, h909, h920, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h922 | h922
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h923 | h923
                          · linarith only [h1, h893, h912, h918, h922, h923, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h925 | h925
                            · linarith only [h1, h893, h912, h920, h925, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h927 | h927
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                                · rcases h3bigk with h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h1, h893, h912, h922, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p929_1, u1elo3]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h895, hlam, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h907, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h909, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h1, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h912, hlam, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h918, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h920, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h925, h928, hc03, hc34, hlam, hphi, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h912, h925, h928, hc12, hc34, hlam, hphi, ht23, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h923, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h925, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    rcases p929_3 (m.d 0 3) (by simp) with h945 | h945
                                    · linarith only [h945, hlam, p929_0]
                                    · rcases p929_3 (m.d 1 3) (by simp) with h947 | h947
                                      · linarith only [h918, h947, hlam]
                                      · rcases p929_3 (m.d 2 3) (by simp) with h949 | h949
                                        · linarith only [h923, h949, hlam]
                                        · linarith only [h895, h949, hlam]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    rcases p929_3 (m.d 0 3) (by simp) with h952 | h952
                                    · linarith only [h907, h952, hlam]
                                    · linarith only [h1, h952, hlam]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h0, h895, hc12, hc34, hlam, hphi, ht23, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h1, h909, h912, hc12, hc34, hlam, hphi, ht23, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    rcases p929_3 (m.d 0 3) (by simp) with h958 | h958
                                    · linarith only [h958, hlam, p929_0]
                                    · rcases p929_3 (m.d 1 3) (by simp) with h960 | h960
                                      · linarith only [h920, h960, hlam]
                                      · rcases p929_3 (m.d 2 3) (by simp) with h962 | h962
                                        · linarith only [h925, h962, hlam]
                                        · linarith only [h895, h962, hlam]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    rcases p929_3 (m.d 0 3) (by simp) with h965 | h965
                                    · linarith only [h909, h965, hlam]
                                    · linarith only [h1, h965, hlam]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h0, h895, hc12, hc35, hlam, hphi, ht23, p929_1]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [h928, hlam, p929_0]
                                  · have p929_0 := h929c.1
                                    have p929_1 := h929c.2.1
                                    have p929_2 := h929c.2.2.1
                                    have p929_3 := h929c.2.2.2
                                    linarith only [hlam, p929_0]
                                · linarith only [h1, h2, h907, h911, h912, h928, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                              · linarith only [h2, h911, h914, h927, hlam]
                        · linarith only [h2, h911, h922, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h974 | h974
              · linarith only [h0, h895, h974, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h976 | h976
                · linarith only [h0, h893, h976, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h978 | h978
                  · linarith only [h0, h893, h978, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                    · linarith only [h1, h893, h895, h907, h980, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                      · linarith only [h1, h893, h982, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                        · linarith only [h2, h911, h984, hc01, hlam, hphi, u1elo3]
                        · linarith only [h1, h2, h974, h984, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
