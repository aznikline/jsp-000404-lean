import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
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
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h0, h11, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h10, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, h4, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, h4, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h1, h20, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h2, h22, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                              · linarith only [h0, h20, h25, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                · linarith only [h0, h15, h22, h24, h25, h27, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h0, h15, h27, h4, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h1, h19, h24, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h19, h31, h4, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h2, h33, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                            · linarith only [h0, h19, h35, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h35, h4, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h0, h40, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h0, h38, h40, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h38, h39, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                  · linarith only [h0, h38, h4, h44, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h38, h4, h46, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h1, h49, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                          · linarith only [h2, h51, h8, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                              · linarith only [h0, h4, h49, h54, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                                · linarith only [h5, h56, h8, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                                  · linarith only [h48, h58, h8, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · rcases h2bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      rcases p60_3 (m.d 0 2) (by simp) with h62 | h62
                                      · rcases p60_3 (m.d 1 2) (by simp) with h63 | h63
                                        · linarith only [h0, h63, hlam]
                                        · rcases p60_3 (m.d 2 3) (by simp) with h65 | h65
                                          · linarith only [h4, h65, hlam]
                                          · linarith only [h38, h65, hlam]
                                      · linarith only [h0, h62, hlam]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h44, h53, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h44, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h44, h53, h54, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, hlam, p60_1]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h38, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h44, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h46, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h4, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h54, hc12, hc35, hlam, hphi, ht23, p60_1]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h44, h54, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h54, hlam, p60_1]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h5, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h53, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h56, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h6, hlam, p60_0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h38, h6, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [h0, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p60_1, u1elo0]
                                    · have p60_0 := h60c.1
                                      have p60_1 := h60c.2.1
                                      have p60_2 := h60c.2.2.1
                                      have p60_3 := h60c.2.2.2
                                      linarith only [hlam, p60_0]
                            · linarith only [h1, h48, h53, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
                        · linarith only [h1, h93, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                          · linarith only [h0, h4, h48, h7, h95, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                            · linarith only [h0, h4, h48, h97, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h38, h4, h7, h97, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h0, h102, h103, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h101, h102, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
                  · linarith only [h0, h101, h107, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                    · linarith only [h0, h101, h109, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                      · linarith only [h1, h111, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h1, h113, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h0, h107, h115, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                            · linarith only [h117, h4, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                              · linarith only [h0, h101, h113, h117, h119, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                                · linarith only [h0, h115, h121, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h0, h100, h101, h117, h121, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                    · linarith only [h0, h126, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h0, h125, h126, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h124, h125, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                  · linarith only [h0, h124, h130, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                    · linarith only [h0, h124, h132, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                      · linarith only [h124, h134, h4, h7, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h136 | h136
                        · linarith only [h1, h136, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h138 | h138
                          · linarith only [h0, h100, h130, h138, h5, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                            · linarith only [h140, h4, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                              · linarith only [h0, h136, h140, h142, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                                · linarith only [h0, h100, h124, h144, h4, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                                  · linarith only [h100, h124, h146, h4, h7, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h124, h146, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h149 | h149
            · rcases m.htr 0 4 5 (by decide) (by decide) with h150 | h150
              · linarith only [h149, h150, h4, h6, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h152 | h152
                · rcases m.htr 1 2 4 (by decide) (by decide) with h153 | h153
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
                    · linarith only [h0, h154, h6, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                        · linarith only [h1, h157, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                          · linarith only [h1, h156, h159, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                            · linarith only [h152, h154, h161, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · linarith only [h152, h154, h156, h161, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                        · linarith only [h149, h156, h164, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h166 | h166
                          · linarith only [h149, h150, h156, h166, h3, h4, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                            · linarith only [h152, h156, h168, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                              · linarith only [h149, h152, h154, h156, h164, h170, h3, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h149, h156, h170, h4, h6, hc13, hc35, hlam, hphi]
                  · linarith only [h153, h5, h6, hc12, hc25, hlam, hphi]
                · linarith only [h152, h4, h6, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
              · linarith only [h175, h5, h6, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
                    · linarith only [h0, h179, h6, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                      · linarith only [h1, h149, h181, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h1, h183, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                          · linarith only [h175, h185, h2, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                            · linarith only [h149, h177, h179, h187, h3, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h189 | h189
                              · linarith only [h1, h177, h183, h189, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h191 | h191
                                · linarith only [h149, h175, h178, h191, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                                  · linarith only [h191, h193, h4, h6, hc23, hc34, hlam, hphi]
                                  · rcases h2bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h6, hc12, hc25, hlam, hphi, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h189, h193, h6, hc23, hc45, hlam, hphi, ht34, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h189, h193, h6, hc24, hc45, hlam, hphi, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h6, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, hlam, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p195_1, u1elo0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h0, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p195_1, u1elo0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h179, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h4, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h177, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h187, hlam, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h189, hlam, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h5, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h178, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h189, h193, h5, h6, hc23, hc45, hlam, hphi, ht34, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h191, hlam, p195_0]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h189, h193, h4, hc23, hc45, hlam, hphi, ht34, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [h177, h189, h193, hc23, hc45, hlam, hphi, ht34, p195_1]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      rcases p195_3 (m.d 0 2) (by simp) with h218 | h218
                                      · linarith only [h218, h6, hlam]
                                      · linarith only [h218, h4, hlam]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      rcases p195_3 (m.d 0 2) (by simp) with h221 | h221
                                      · linarith only [h221, h6, hlam]
                                      · linarith only [h221, h5, hlam]
                                    · have p195_0 := h195c.1
                                      have p195_1 := h195c.2.1
                                      have p195_2 := h195c.2.2.1
                                      have p195_3 := h195c.2.2.2
                                      linarith only [hlam, p195_0]
                  · linarith only [h178, h5, h6, hc12, hc25, hlam, hphi]
                · linarith only [h177, h4, h6, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h227 | h227
          · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
            · linarith only [h228, h4, h5, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h230 | h230
              · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
                · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
                  · linarith only [h227, h232, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h234 | h234
                    · linarith only [h2, h232, h234, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h227, h234, h5, hc12, hc24, hlam, hphi]
                · linarith only [h231, h4, h5, hc12, hc24, hlam, hphi]
              · linarith only [h227, h230, h5, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h239 | h239
            · linarith only [h239, h4, h5, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                  · linarith only [h0, h243, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                    · linarith only [h0, h227, h245, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
                      · linarith only [h239, h241, h247, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
                        · linarith only [h1, h249, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
                          · linarith only [h2, h251, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · linarith only [h2, h241, h242, h243, h251, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h227, h242, h4, hc12, hc25, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                  · linarith only [h0, h256, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                    · linarith only [h0, h227, h258, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                      · linarith only [h1, h239, h260, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                        · linarith only [h1, h262, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h264 | h264
                          · linarith only [h2, h241, h264, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                            · linarith only [h239, h255, h266, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h268 | h268
                              · linarith only [h255, h256, h262, h264, h268, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                                · linarith only [h0, h241, h255, h266, h270, h5, hc23, hc34, hlam, hphi]
                                · linarith only [h0, h255, h270, h5, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h255, h4, h5, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h274 | h274
        · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
          · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
            · rcases m.htr 0 4 5 (by decide) (by decide) with h277 | h277
              · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
                · linarith only [h274, h277, h278, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h280 | h280
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h281 | h281
                    · linarith only [h1, h278, h281, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h275, h281, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h274, h280, h4, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
                · linarith only [h274, h285, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h1, h285, h288, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h275, h288, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h274, h287, h4, hc12, hc23, hlam, hphi]
            · linarith only [h274, h276, h4, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
            · rcases m.htr 0 4 5 (by decide) (by decide) with h294 | h294
              · linarith only [h274, h275, h294, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                · linarith only [h274, h296, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h0, h275, h299, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
                        · linarith only [h1, h302, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h304 | h304
                          · linarith only [h2, h294, h304, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                                · linarith only [h294, h296, h298, h3, h302, h308, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                                  · linarith only [h296, h298, h302, h306, h307, h308, h310, hlam]
                                  · rcases h2bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h0, h298, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p312_1, u1elo0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h4, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h275, h306, h308, hc34, hc45, hlam, hphi, p312_1]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h275, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h0, hlam, p312_1]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h296, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h0, h306, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p312_1, u1elo0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h299, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      rcases p312_3 (m.d 0 2) (by simp) with h323 | h323
                                      · linarith only [h323, hlam, p312_0]
                                      · rcases p312_3 (m.d 1 2) (by simp) with h325 | h325
                                        · linarith only [h296, h325, hlam]
                                        · rcases p312_3 (m.d 2 3) (by simp) with h327 | h327
                                          · rcases p312_3 (m.d 2 4) (by simp) with h328 | h328
                                            · linarith only [h306, h328, hlam]
                                            · rcases p312_3 (m.d 2 5) (by simp) with h330 | h330
                                              · linarith only [h307, h330, hlam]
                                              · linarith only [h275, h330, hlam]
                                          · linarith only [h327, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      rcases p312_3 (m.d 0 2) (by simp) with h334 | h334
                                      · linarith only [h334, h4, hlam]
                                      · linarith only [h0, h334, hlam]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h296, h298, h302, h307, hlam, p312_2]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h275, hc02, hc23, hlam, hphi, p312_1]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h274, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h298, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h306, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h308, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h0, h298, h306, h308, hc34, hc45, hlam, hphi, p312_1]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h298, h306, h308, hc34, hc45, hlam, hphi, p312_1]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [h307, hlam, p312_0]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      rcases p312_3 (m.d 0 2) (by simp) with h348 | h348
                                      · linarith only [h275, h348, hlam]
                                      · linarith only [h274, h348, hlam]
                                    · have p312_0 := h312c.1
                                      have p312_1 := h312c.2.1
                                      have p312_2 := h312c.2.2.1
                                      have p312_3 := h312c.2.2.2
                                      linarith only [hlam, p312_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h352 | h352
                                · linarith only [h298, h352, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h354 | h354
                                  · linarith only [h0, h298, h306, h307, h352, h354, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                  · linarith only [h0, h298, h306, h307, h354, h4, hc34, hc45, hlam, hphi]
                            · linarith only [h293, h306, h4, hlam]
                      · linarith only [h1, h293, h296, h298, h301, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h274, h298, h4, hc12, hc23, hlam, hphi]
            · linarith only [h274, h293, h4, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h361 | h361
          · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
            · rcases m.htr 0 4 5 (by decide) (by decide) with h363 | h363
              · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                · linarith only [h361, h364, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
                  · linarith only [h1, h274, h361, h364, h366, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h368 | h368
                    · linarith only [h1, h364, h368, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h361, h368, h4, hc12, hc23, hlam, hphi]
              · linarith only [h274, h361, h363, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
              · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                · linarith only [h361, h373, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
                  · linarith only [h1, h274, h361, h373, h375, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                    · linarith only [h1, h373, h377, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · linarith only [h361, h377, h4, hc12, hc23, hlam, hphi]
              · linarith only [h274, h361, h372, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h381 | h381
            · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
                · linarith only [h0, h383, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                  · linarith only [h274, h382, h385, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                    · linarith only [h0, h361, h387, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
                        · linarith only [h1, h390, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                          · linarith only [h3, h389, h390, h392, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h395 | h395
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h396 | h396
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h397 | h397
                                  · linarith only [h389, h390, h392, h397, hlam]
                                  · linarith only [h1, h381, h382, h389, h390, h397, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h274, h382, h396, hlam]
                              · linarith only [h381, h382, h385, h392, h395, h4, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h381, h382, h385, h389, h392, h394, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h1, h381, h389, h403, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h405 | h405
                          · linarith only [h2, h405, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h409 | h409
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
                                  · linarith only [h1, h381, h383, h389, h405, h410, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · linarith only [h274, h382, h383, h389, h410, hc12, hc24, hlam, hphi]
                                · linarith only [h0, h1, h274, h381, h382, h409, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                              · linarith only [h381, h383, h389, h4, h408, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h381, h382, h383, h389, h4, h405, h407, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                · linarith only [h0, h381, h4, h416, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                  · linarith only [h0, h274, h418, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                    · linarith only [h1, h416, h420, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h422 | h422
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h423 | h423
                        · linarith only [h1, h423, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h425 | h425
                          · linarith only [h3, h422, h423, h425, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h428 | h428
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h429 | h429
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
                                  · linarith only [h1, h274, h381, h382, h430, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                  · rcases h2bigk with h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c | h432c
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h274, h382, h427, h429, hc12, hc23, hlam, hphi, p432_1]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h4, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h274, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h361, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h0, hlam, p432_1]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h416, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h418, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h420, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      rcases p432_3 (m.d 0 2) (by simp) with h443 | h443
                                      · linarith only [h443, hlam, p432_0]
                                      · rcases p432_3 (m.d 1 2) (by simp) with h445 | h445
                                        · linarith only [h416, h445, hlam]
                                        · rcases p432_3 (m.d 2 3) (by simp) with h447 | h447
                                          · rcases p432_3 (m.d 2 4) (by simp) with h448 | h448
                                            · linarith only [h427, h448, hlam]
                                            · linarith only [h274, h448, hlam]
                                          · linarith only [h447, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      rcases p432_3 (m.d 0 2) (by simp) with h452 | h452
                                      · linarith only [h4, h452, hlam]
                                      · linarith only [h0, h452, hlam]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h422, h423, h429, h430, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p432_1]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h422, h423, h429, h430, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p432_1]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      rcases p432_3 (m.d 0 2) (by simp) with h458 | h458
                                      · linarith only [h458, hlam, p432_0]
                                      · rcases p432_3 (m.d 1 2) (by simp) with h460 | h460
                                        · linarith only [h418, h460, hlam]
                                        · rcases p432_3 (m.d 2 3) (by simp) with h462 | h462
                                          · rcases p432_3 (m.d 2 4) (by simp) with h463 | h463
                                            · rcases p432_3 (m.d 2 5) (by simp) with h464 | h464
                                              · linarith only [h429, h464, hlam]
                                              · linarith only [h361, h464, hlam]
                                            · linarith only [h463, hlam, p432_0]
                                          · linarith only [h4, h462, hlam]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      rcases p432_3 (m.d 0 2) (by simp) with h469 | h469
                                      · linarith only [h274, h469, hlam]
                                      · linarith only [h0, h469, hlam]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h427, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h422, h423, h429, h430, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p432_1]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      rcases p432_3 (m.d 0 2) (by simp) with h475 | h475
                                      · linarith only [h475, hlam, p432_0]
                                      · rcases p432_3 (m.d 1 2) (by simp) with h477 | h477
                                        · linarith only [h420, h477, hlam]
                                        · rcases p432_3 (m.d 2 3) (by simp) with h479 | h479
                                          · rcases p432_3 (m.d 2 4) (by simp) with h480 | h480
                                            · rcases p432_3 (m.d 2 5) (by simp) with h481 | h481
                                              · rcases h4bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h382, hc14, hc45, hlam, hphi, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h274, hlam, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h382, hc34, hc45, hlam, hphi, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h382, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h2, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h418, hlam, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p482_1, u1elo0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h425, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  rcases p482_3 (m.d 0 4) (by simp) with h493 | h493
                                                  · linarith only [h274, h493, hlam]
                                                  · rcases p482_3 (m.d 1 4) (by simp) with h495 | h495
                                                    · linarith only [h418, h495, hlam]
                                                    · rcases p482_3 (m.d 2 4) (by simp) with h497 | h497
                                                      · rcases p482_3 (m.d 3 4) (by simp) with h498 | h498
                                                        · linarith only [h427, h498, hlam]
                                                        · rcases p482_3 (m.d 4 5) (by simp) with h500 | h500
                                                          · linarith only [h429, h500, hlam]
                                                          · linarith only [h382, h500, hlam]
                                                      · linarith only [h274, h497, hlam]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  rcases p482_3 (m.d 0 4) (by simp) with h504 | h504
                                                  · linarith only [h274, h504, hlam]
                                                  · linarith only [h2, h504, hlam]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h422, h423, h429, h430, hlam, p482_2]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h0, h274, h382, h427, hc12, hc23, hlam, hphi, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h381, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h422, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h427, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h430, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h0, h274, h427, h429, hc12, hc23, hlam, hphi, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h418, h427, h429, hc12, hc23, hlam, hphi, p482_1]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [h429, hlam, p482_0]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  rcases p482_3 (m.d 0 4) (by simp) with h518 | h518
                                                  · linarith only [h382, h518, hlam]
                                                  · linarith only [h381, h518, hlam]
                                                · have p482_0 := h482c.1
                                                  have p482_1 := h482c.2.1
                                                  have p482_2 := h482c.2.2.1
                                                  have p482_3 := h482c.2.2.2
                                                  linarith only [hlam, p482_0]
                                              · linarith only [h481, hlam, p432_0]
                                            · linarith only [h274, h480, hlam]
                                          · linarith only [h4, h479, hlam]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      rcases p432_3 (m.d 0 2) (by simp) with h525 | h525
                                      · linarith only [h361, h525, hlam]
                                      · linarith only [h0, h525, hlam]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h428, hlam, p432_0]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [h429, hlam, p432_1]
                                    · have p432_0 := h432c.1
                                      have p432_1 := h432c.2.1
                                      have p432_2 := h432c.2.2.1
                                      have p432_3 := h432c.2.2.2
                                      linarith only [hlam, p432_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h531 | h531
                                  · linarith only [h422, h429, h531, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                                  · rcases h2bigk with h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h274, hc12, hc24, hlam, hphi, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h4, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h274, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h361, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h0, hlam, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h416, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h418, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h420, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      rcases p533_3 (m.d 0 2) (by simp) with h544 | h544
                                      · linarith only [h544, hlam, p533_0]
                                      · rcases p533_3 (m.d 1 2) (by simp) with h546 | h546
                                        · linarith only [h416, h546, hlam]
                                        · rcases p533_3 (m.d 2 3) (by simp) with h548 | h548
                                          · rcases p533_3 (m.d 2 4) (by simp) with h549 | h549
                                            · linarith only [h427, h549, hlam]
                                            · linarith only [h274, h549, hlam]
                                          · linarith only [h548, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      rcases p533_3 (m.d 0 2) (by simp) with h553 | h553
                                      · linarith only [h4, h553, hlam]
                                      · linarith only [h0, h553, hlam]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h274, hc02, hc23, hlam, hphi, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h422, h423, h428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h0, h429, hc12, hc45, hlam, hphi, ht23, ht34, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h429, hc12, hc45, hlam, hphi, ht23, ht34, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h427, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h429, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      rcases p533_3 (m.d 0 2) (by simp) with h564 | h564
                                      · linarith only [h564, hlam, p533_0]
                                      · rcases p533_3 (m.d 1 2) (by simp) with h566 | h566
                                        · linarith only [h420, h566, hlam]
                                        · rcases p533_3 (m.d 2 3) (by simp) with h568 | h568
                                          · rcases p533_3 (m.d 2 4) (by simp) with h569 | h569
                                            · linarith only [h429, h569, hlam]
                                            · linarith only [h274, h569, hlam]
                                          · linarith only [h4, h568, hlam]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      rcases p533_3 (m.d 0 2) (by simp) with h573 | h573
                                      · linarith only [h361, h573, hlam]
                                      · linarith only [h0, h573, hlam]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h428, hlam, p533_0]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [h0, h274, hc12, hc25, hlam, hphi, p533_1]
                                    · have p533_0 := h533c.1
                                      have p533_1 := h533c.2.1
                                      have p533_2 := h533c.2.2.1
                                      have p533_3 := h533c.2.2.2
                                      linarith only [hlam, p533_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h579 | h579
                                · linarith only [h0, h274, h382, h427, h428, h579, hc12, hc35, hlam, hphi, ht23]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h581 | h581
                                  · linarith only [h422, h579, h581, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                                  · rcases h2bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h274, h427, hc12, hc23, hlam, hphi, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h4, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h274, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h361, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h0, hlam, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h416, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h418, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h420, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h428, h581, hc02, hc45, hlam, hphi, ht23, ht34, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h428, h581, hc12, hc45, hlam, hphi, ht23, ht34, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h428, h581, hc24, hc45, hlam, hphi, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h428, hlam, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h0, h427, h428, h581, hc12, hc45, hlam, hphi, ht23, ht34, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h427, h428, h581, hc12, hc45, hlam, hphi, ht23, ht34, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h427, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h579, hlam, p583_0]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      rcases p583_3 (m.d 0 2) (by simp) with h604 | h604
                                      · linarith only [h604, hlam, p583_0]
                                      · rcases p583_3 (m.d 1 2) (by simp) with h606 | h606
                                        · linarith only [h420, h606, hlam]
                                        · rcases p583_3 (m.d 2 3) (by simp) with h608 | h608
                                          · linarith only [h428, h608, hlam]
                                          · linarith only [h4, h608, hlam]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      rcases p583_3 (m.d 0 2) (by simp) with h611 | h611
                                      · linarith only [h361, h611, hlam]
                                      · linarith only [h0, h611, hlam]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h0, h4, h428, h581, hc12, hc45, hlam, hphi, ht23, ht34, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [h0, h274, h428, h581, hc12, hc45, hlam, hphi, ht23, ht34, p583_1]
                                    · have p583_0 := h583c.1
                                      have p583_1 := h583c.2.1
                                      have p583_2 := h583c.2.2.1
                                      have p583_3 := h583c.2.2.2
                                      linarith only [hlam, p583_0]
                            · linarith only [h0, h2, h4, h422, h427, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h618 | h618
                        · linarith only [h1, h618, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
                          · linarith only [h1, h381, h422, h620, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h623 | h623
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h624 | h624
                                · linarith only [h381, h382, h416, h422, h624, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h626 | h626
                                  · linarith only [h1, h381, h624, h626, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                  · rcases h2bigk with h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h4, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h274, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h361, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h0, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h416, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h418, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h420, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      rcases p628_3 (m.d 0 2) (by simp) with h639 | h639
                                      · linarith only [h639, hlam, p628_0]
                                      · rcases p628_3 (m.d 1 2) (by simp) with h641 | h641
                                        · linarith only [h416, h641, hlam]
                                        · rcases p628_3 (m.d 2 3) (by simp) with h643 | h643
                                          · rcases p628_3 (m.d 2 4) (by simp) with h644 | h644
                                            · linarith only [h622, h644, hlam]
                                            · linarith only [h274, h644, hlam]
                                          · linarith only [h643, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      rcases p628_3 (m.d 0 2) (by simp) with h648 | h648
                                      · linarith only [h4, h648, hlam]
                                      · linarith only [h0, h648, hlam]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h274, h381, h416, h422, hc12, hc23, hlam, hphi, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h361, hc02, hc23, hlam, hphi, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h0, h624, hc12, hc45, hlam, hphi, ht23, ht34, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h624, hc12, hc45, hlam, hphi, ht23, ht34, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h622, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h624, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      rcases p628_3 (m.d 0 2) (by simp) with h659 | h659
                                      · linarith only [h659, hlam, p628_0]
                                      · rcases p628_3 (m.d 1 2) (by simp) with h661 | h661
                                        · linarith only [h420, h661, hlam]
                                        · rcases p628_3 (m.d 2 3) (by simp) with h663 | h663
                                          · rcases p628_3 (m.d 2 4) (by simp) with h664 | h664
                                            · linarith only [h624, h664, hlam]
                                            · linarith only [h274, h664, hlam]
                                          · linarith only [h4, h663, hlam]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      rcases p628_3 (m.d 0 2) (by simp) with h668 | h668
                                      · linarith only [h361, h668, hlam]
                                      · linarith only [h0, h668, hlam]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h623, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h0, h274, hc12, hc25, hlam, hphi, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                              · linarith only [h381, h4, h416, h422, h623, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h381, h4, h622, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h676 | h676
              · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                · linarith only [h0, h4, h677, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                  · linarith only [h274, h676, h679, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
                    · linarith only [h1, h677, h681, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h683 | h683
                      · linarith only [h1, h381, h4, h683, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h685 | h685
                        · linarith only [h1, h685, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h687 | h687
                          · linarith only [h2, h687, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h689 | h689
                            · linarith only [h381, h676, h677, h683, h687, h689, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h691 | h691
                              · linarith only [h677, h685, h689, h691, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                                  · rcases h2bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h4, h691, h694, hc12, hc34, hlam, hphi, ht23, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h4, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h274, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h361, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h0, hlam, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h677, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h679, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h681, hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h691, h694, hc02, hc34, hlam, hphi, ht23, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h691, h694, hc12, hc34, hlam, hphi, ht23, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h689, hlam, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h691, hlam, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      rcases p695_3 (m.d 0 2) (by simp) with h711 | h711
                                      · linarith only [h711, hlam, p695_0]
                                      · rcases p695_3 (m.d 1 2) (by simp) with h713 | h713
                                        · linarith only [h679, h713, hlam]
                                        · rcases p695_3 (m.d 2 3) (by simp) with h715 | h715
                                          · linarith only [h689, h715, hlam]
                                          · linarith only [h4, h715, hlam]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      rcases p695_3 (m.d 0 2) (by simp) with h718 | h718
                                      · linarith only [h274, h718, hlam]
                                      · linarith only [h0, h718, hlam]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h361, h676, h677, h683, h687, h689, hc12, hc34, hlam, hphi, ht23, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      rcases p695_3 (m.d 0 2) (by simp) with h724 | h724
                                      · linarith only [h724, hlam, p695_0]
                                      · rcases p695_3 (m.d 1 2) (by simp) with h726 | h726
                                        · linarith only [h681, h726, hlam]
                                        · rcases p695_3 (m.d 2 3) (by simp) with h728 | h728
                                          · linarith only [h691, h728, hlam]
                                          · linarith only [h4, h728, hlam]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      rcases p695_3 (m.d 0 2) (by simp) with h731 | h731
                                      · linarith only [h361, h731, hlam]
                                      · linarith only [h0, h731, hlam]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [h693, hlam, p695_1]
                                    · have p695_0 := h695c.1
                                      have p695_1 := h695c.2.1
                                      have p695_2 := h695c.2.2.1
                                      have p695_3 := h695c.2.2.2
                                      linarith only [hlam, p695_0]
                                  · linarith only [h2, h676, h689, h693, h694, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
                                · linarith only [h274, h676, h693, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
                · linarith only [h0, h4, h739, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                  · linarith only [h0, h274, h741, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                    · linarith only [h0, h361, h743, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                      · linarith only [h1, h381, h4, h745, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                        · linarith only [h1, h747, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
                          · linarith only [h2, h381, h4, h676, h749, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h752 | h752
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                                  · linarith only [h0, h381, h4, h676, h751, h754, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h381, h4, h753, h754, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h757 | h757
                                  · linarith only [h0, h274, h753, h757, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h2bigk with h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c | h759c
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h381, h4, h751, hc12, hc24, hlam, hphi, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h4, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h274, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h361, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h0, hlam, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h739, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h741, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h743, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      rcases p759_3 (m.d 0 2) (by simp) with h770 | h770
                                      · linarith only [h770, hlam, p759_0]
                                      · rcases p759_3 (m.d 1 2) (by simp) with h772 | h772
                                        · linarith only [h739, h772, hlam]
                                        · rcases p759_3 (m.d 2 3) (by simp) with h774 | h774
                                          · rcases p759_3 (m.d 2 4) (by simp) with h775 | h775
                                            · linarith only [h751, h775, hlam]
                                            · linarith only [h274, h775, hlam]
                                          · linarith only [h774, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      rcases p759_3 (m.d 0 2) (by simp) with h779 | h779
                                      · linarith only [h4, h779, hlam]
                                      · linarith only [h0, h779, hlam]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h381, h4, h751, hc02, hc23, hlam, hphi, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h0, h361, hc12, hc23, hlam, hphi, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h0, h753, hc12, hc45, hlam, hphi, ht23, ht34, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h753, hc12, hc45, hlam, hphi, ht23, ht34, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h751, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h753, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      rcases p759_3 (m.d 0 2) (by simp) with h790 | h790
                                      · linarith only [h790, hlam, p759_0]
                                      · rcases p759_3 (m.d 1 2) (by simp) with h792 | h792
                                        · linarith only [h743, h792, hlam]
                                        · rcases p759_3 (m.d 2 3) (by simp) with h794 | h794
                                          · rcases p759_3 (m.d 2 4) (by simp) with h795 | h795
                                            · linarith only [h753, h795, hlam]
                                            · linarith only [h274, h795, hlam]
                                          · linarith only [h4, h794, hlam]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      rcases p759_3 (m.d 0 2) (by simp) with h799 | h799
                                      · linarith only [h361, h799, hlam]
                                      · linarith only [h0, h799, hlam]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h752, hlam, p759_0]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [h0, h274, hc12, hc25, hlam, hphi, p759_1]
                                    · have p759_0 := h759c.1
                                      have p759_1 := h759c.2.1
                                      have p759_2 := h759c.2.2.1
                                      have p759_3 := h759c.2.2.2
                                      linarith only [hlam, p759_0]
                              · linarith only [h0, h381, h4, h751, h752, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h806 | h806
                              · linarith only [h747, h751, h806, hc13, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h808 | h808
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h809 | h809
                                  · rcases h2bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h4, h806, h809, hc12, hc34, hlam, hphi, ht23, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h4, hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h274, hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h361, hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h0, hlam, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h739, hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h741, hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h743, hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h806, h809, hc02, hc34, hlam, hphi, ht23, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h806, h809, hc12, hc34, hlam, hphi, ht23, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h751, hlam, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h806, hlam, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      rcases p810_3 (m.d 0 2) (by simp) with h826 | h826
                                      · linarith only [h826, hlam, p810_0]
                                      · rcases p810_3 (m.d 1 2) (by simp) with h828 | h828
                                        · linarith only [h741, h828, hlam]
                                        · rcases p810_3 (m.d 2 3) (by simp) with h830 | h830
                                          · linarith only [h751, h830, hlam]
                                          · linarith only [h4, h830, hlam]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      rcases p810_3 (m.d 0 2) (by simp) with h833 | h833
                                      · linarith only [h274, h833, hlam]
                                      · linarith only [h0, h833, hlam]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h0, h4, h751, hc12, hc34, hlam, hphi, ht23, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [hlam, p810_0]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h0, h361, h751, hc12, hc34, hlam, hphi, ht23, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      rcases p810_3 (m.d 0 2) (by simp) with h839 | h839
                                      · linarith only [h839, hlam, p810_0]
                                      · rcases p810_3 (m.d 1 2) (by simp) with h841 | h841
                                        · linarith only [h743, h841, hlam]
                                        · rcases p810_3 (m.d 2 3) (by simp) with h843 | h843
                                          · linarith only [h806, h843, hlam]
                                          · linarith only [h4, h843, hlam]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      rcases p810_3 (m.d 0 2) (by simp) with h846 | h846
                                      · linarith only [h361, h846, hlam]
                                      · linarith only [h0, h846, hlam]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [h808, hlam, p810_1]
                                    · have p810_0 := h810c.1
                                      have p810_1 := h810c.2.1
                                      have p810_2 := h810c.2.2.1
                                      have p810_3 := h810c.2.2.2
                                      linarith only [hlam, p810_0]
                                  · linarith only [h751, h808, h809, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h853 | h853
                                  · linarith only [h0, h274, h808, h853, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h4, h751, h853, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h856 | h856
      · rcases m.htr 0 2 4 (by decide) (by decide) with h857 | h857
        · rcases m.htr 0 2 5 (by decide) (by decide) with h858 | h858
          · linarith only [h0, h3, h858, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h860 | h860
            · rcases m.htr 0 4 5 (by decide) (by decide) with h861 | h861
              · linarith only [h2, h3, h861, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h863 | h863
                · linarith only [h0, h3, h863, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h0, h3, h856, h863, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h866 | h866
              · linarith only [h0, h3, h857, h866, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h868 | h868
                · linarith only [h0, h3, h868, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h0, h3, h856, h868, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h871 | h871
          · linarith only [h2, h3, h857, h871, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h873 | h873
            · linarith only [h856, h857, h873, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h875 | h875
              · linarith only [h2, h3, h875, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h877 | h877
                · linarith only [h0, h3, h877, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h2, h3, h856, h857, h877, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h880 | h880
        · rcases m.htr 0 2 5 (by decide) (by decide) with h881 | h881
          · linarith only [h0, h3, h881, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
            · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
              · linarith only [h1, h3, h856, h880, h884, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                · linarith only [h856, h880, h886, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h888 | h888
                  · linarith only [h1, h3, h886, h888, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                  · linarith only [h856, h880, h888, hc12, hc23, hlam, hphi]
            · linarith only [h856, h880, h883, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h892 | h892
          · linarith only [h1, h3, h856, h892, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h894 | h894
            · rcases m.htr 0 4 5 (by decide) (by decide) with h895 | h895
              · linarith only [h1, h3, h894, h895, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
                · linarith only [h0, h3, h897, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
                  · linarith only [h1, h3, h880, h897, h899, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h901 | h901
                    · linarith only [h0, h3, h892, h901, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                      · linarith only [h1, h3, h903, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · linarith only [h1, h3, h894, h897, h903, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h906 | h906
              · linarith only [h2, h3, h906, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
                · linarith only [h0, h3, h856, h908, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h910 | h910
                  · linarith only [h0, h3, h880, h894, h910, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h912 | h912
                    · linarith only [h0, h3, h892, h912, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                      · linarith only [h0, h1, h3, h856, h894, h914, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h916 | h916
                        · linarith only [h1, h3, h916, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h918 | h918
                          · linarith only [h2, h3, h856, h894, h906, h918, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h920 | h920
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h921 | h921
                              · linarith only [h0, h3, h916, h921, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h856, h894, h920, h921, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h924 | h924
                              · linarith only [h2, h3, h908, h914, h916, h924, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                                · linarith only [h2, h3, h908, h914, h918, h920, h926, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                                  · linarith only [h0, h856, h920, h926, h928, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h856, h920, h928, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h931 | h931
    · linarith only [h2, h931, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h933 | h933
      · rcases m.htr 0 2 4 (by decide) (by decide) with h934 | h934
        · linarith only [h0, h2, h934, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h936 | h936
          · linarith only [h0, h2, h936, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h938 | h938
            · linarith only [h1, h2, h938, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h940 | h940
              · rcases m.htr 1 2 3 (by decide) (by decide) with h941 | h941
                · linarith only [h0, h2, h941, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h933, h941, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h944 | h944
                · linarith only [h0, h2, h944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · linarith only [h0, h2, h933, h944, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h947 | h947
        · linarith only [h1, h2, h933, h947, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h949 | h949
          · linarith only [h1, h2, h933, h949, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h951 | h951
            · linarith only [h1, h2, h951, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h953 | h953
              · rcases m.htr 1 2 3 (by decide) (by decide) with h954 | h954
                · linarith only [h0, h2, h933, h954, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
                  · linarith only [h947, h953, h956, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h958 | h958
                    · linarith only [h1, h2, h949, h954, h958, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                      · linarith only [h1, h2, h951, h960, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h962 | h962
                        · linarith only [h1, h2, h962, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h964 | h964
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h965 | h965
                            · linarith only [h1, h931, h954, h960, h964, h965, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h967 | h967
                              · linarith only [h1, h931, h954, h962, h965, h967, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h969 | h969
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                                  · rcases h2bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h0, h931, h964, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p971_1, u1elo3]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h933, hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h947, hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h949, hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h0, hlam, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h954, hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h956, hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h958, hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h967, h970, hc02, hc34, hlam, hphi, ht23, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h967, h970, hc12, hc34, hlam, hphi, ht23, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h965, hlam, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h967, hlam, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      rcases p971_3 (m.d 0 2) (by simp) with h987 | h987
                                      · linarith only [h987, hlam, p971_0]
                                      · rcases p971_3 (m.d 1 2) (by simp) with h989 | h989
                                        · linarith only [h956, h989, hlam]
                                        · rcases p971_3 (m.d 2 3) (by simp) with h991 | h991
                                          · linarith only [h965, h991, hlam]
                                          · linarith only [h933, h991, hlam]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      rcases p971_3 (m.d 0 2) (by simp) with h994 | h994
                                      · linarith only [h947, h994, hlam]
                                      · linarith only [h0, h994, hlam]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h0, h933, hc12, hc24, hlam, hphi, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [hlam, p971_0]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h931, h958, h965, hc01, hc34, hlam, hphi, ht12, ht23, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      rcases p971_3 (m.d 0 2) (by simp) with h1000 | h1000
                                      · linarith only [h1000, hlam, p971_0]
                                      · rcases p971_3 (m.d 1 2) (by simp) with h1002 | h1002
                                        · linarith only [h1002, h958, hlam]
                                        · rcases p971_3 (m.d 2 3) (by simp) with h1004 | h1004
                                          · linarith only [h1004, h967, hlam]
                                          · linarith only [h1004, h933, hlam]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      rcases p971_3 (m.d 0 2) (by simp) with h1007 | h1007
                                      · linarith only [h1007, h949, hlam]
                                      · linarith only [h0, h1007, hlam]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h0, h933, hc12, hc25, hlam, hphi, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [h969, hlam, p971_1]
                                    · have p971_0 := h971c.1
                                      have p971_1 := h971c.2.1
                                      have p971_2 := h971c.2.2.1
                                      have p971_3 := h971c.2.2.2
                                      linarith only [hlam, p971_0]
                                  · linarith only [h2, h953, h965, h969, h970, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                                · linarith only [h1, h931, h953, h954, h956, h964, h969, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h2, h954, h964, hc12, hc45, hlam, hphi, ht23, ht34]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1016 | h1016
                · linarith only [h0, h1016, h933, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1018 | h1018
                  · linarith only [h0, h1018, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1020 | h1020
                    · linarith only [h1, h1016, h1020, h2, h949, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
                      · linarith only [h1, h1022, h2, h951, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1024 | h1024
                        · linarith only [h1, h1024, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1026 | h1026
                          · linarith only [h1, h1016, h1026, h2, h953, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h1, h1016, h1026, h2, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
