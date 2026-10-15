import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3618000 in
theorem r1l7_10_12_13_25_L_I_L_0_L_I_M_IR_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
          · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
            · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
              · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                          · linarith only [h0, h16, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · linarith only [h15, h16, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h1, h12, h15, h19, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                            · linarith only [h21, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h1, h12, h15, h21, h23, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                              · linarith only [h15, h23, h3, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                          · linarith only [h27, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · linarith only [h13, h14, h26, h27, h3, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h12, h14, h26, h3, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h12, h13, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h12, h3, h32, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h12, h3, h34, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                        · linarith only [h12, h3, h34, h36, h6, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h12, h3, h32, h34, h38, h6, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h12, h34, h4, h40, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                              · linarith only [h12, h3, h34, h42, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                              · linarith only [h12, h3, h42, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
              · linarith only [h10, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                      · linarith only [h2, h53, h8, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h3, h56, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · linarith only [h1, h3, h52, h55, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                          · linarith only [h3, h59, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                            · linarith only [h1, h3, h51, h55, h61, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                              · linarith only [h6, h63, h8, hlam]
                              · rcases h0emin with h65 | h65 | h65 | h65 | h65
                                · rcases h3bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, h52, h55, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    rcases p66_3 (m.d 0 3) (by simp) with h69 | h69
                                    · rcases p66_3 (m.d 1 3) (by simp) with h70 | h70
                                      · linarith only [h1, h70, hlam]
                                      · linarith only [h48, h70, hlam]
                                    · linarith only [h3, h69, hlam]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, h55, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, h55, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    rcases p66_3 (m.d 0 3) (by simp) with h78 | h78
                                    · rcases p66_3 (m.d 1 3) (by simp) with h79 | h79
                                      · rcases p66_3 (m.d 2 3) (by simp) with h80 | h80
                                        · linarith only [h48, h80, hlam]
                                        · rcases p66_3 (m.d 3 4) (by simp) with h82 | h82
                                          · linarith only [h51, h82, hlam]
                                          · linarith only [h55, h82, hlam]
                                      · linarith only [h48, h79, hlam]
                                    · linarith only [h3, h78, hlam]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p66_1]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, h3, h55, h63, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h48, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h55, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h59, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h6, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h51, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h63, hlam, p66_1]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h7, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h52, hlam, p66_0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, h3, h52, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [h1, h3, h52, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p66_1, u2elo0]
                                  · have p66_0 := h66c.1
                                    have p66_1 := h66c.2.1
                                    have p66_2 := h66c.2.2.1
                                    have p66_3 := h66c.2.2.2
                                    linarith only [hlam, p66_0]
                                · linarith only [h65, hlam, ht01, ht12, u2elo0]
                                · linarith only [h3, h65, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h65, hlam, ht01, ht12, u2elo0]
                                · linarith only [h3, h65, h7, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h51, h52, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                    · linarith only [h109, h3, h51, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h0, h111, h49, h51, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                        · linarith only [h113, h48, h51, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h109, h115, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                            · linarith only [h117, h4, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                              · linarith only [h119, h6, h8, hlam]
                              · rcases h0emin with h121 | h121 | h121 | h121 | h121
                                · rcases h3bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    rcases p122_3 (m.d 0 3) (by simp) with h124 | h124
                                    · rcases p122_3 (m.d 1 3) (by simp) with h125 | h125
                                      · linarith only [h1, h125, hlam]
                                      · rcases p122_3 (m.d 2 3) (by simp) with h127 | h127
                                        · linarith only [h127, h3, hlam]
                                        · rcases p122_3 (m.d 3 4) (by simp) with h129 | h129
                                          · linarith only [h129, h6, hlam]
                                          · linarith only [h129, h51, hlam]
                                    · linarith only [h1, h124, hlam]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    rcases p122_3 (m.d 0 3) (by simp) with h133 | h133
                                    · rcases p122_3 (m.d 1 3) (by simp) with h134 | h134
                                      · linarith only [h1, h134, hlam]
                                      · linarith only [h134, h48, hlam]
                                    · linarith only [h133, h3, hlam]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, h51, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht5b, p122_1, u2elo0, u5ehi3]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h1, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h51, hc23, hc34, hlam, hphi, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h51, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h109, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h48, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h113, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h115, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h6, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h119, hlam, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h7, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, h48, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p122_1, u2elo0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p122_1, u2elo0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                · linarith only [h121, hlam, ht01, ht12, u2elo0]
                                · linarith only [h121, h3, hlam, ht01, ht12, u2elo0]
                                · linarith only [h121, h8, hc45, hlam, ht01, ht12, ht23, ht34]
                                · linarith only [h121, h3, h7, hlam, ht01, ht12, u2elo0]
                · linarith only [h5, h50, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h48, h49, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h3, h48, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
          · linarith only [h167, h6, h7, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h1, h173, h7, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                      · linarith only [h1, h167, h172, h175, h7, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                          · linarith only [h178, h3, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                            · linarith only [h180, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h182 | h182
                              · linarith only [h167, h171, h177, h178, h182, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h0emin with h184 | h184 | h184 | h184 | h184
                                · rcases h3bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h182, h7, hc13, hc45, hlam, hphi, ht34, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h177, h182, h7, hc34, hc45, hlam, hphi, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h182, h7, hc34, hc45, hlam, hphi, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h7, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h1, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h1, h177, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h1, h182, h7, hc34, hc45, hlam, hphi, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h173, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h3, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h169, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h0, h171, h178, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p185_1, u2elo0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h178, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h6, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h172, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h177, hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [hlam, p185_0]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h182, hlam, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h182, h6, hc34, hc45, hlam, hphi, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h172, h182, hc34, hc45, hlam, hphi, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [h177, h182, hc34, hc45, hlam, hphi, p185_1]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    rcases p185_3 (m.d 0 3) (by simp) with h209 | h209
                                    · linarith only [h209, h7, hlam]
                                    · linarith only [h209, h6, hlam]
                                  · have p185_0 := h185c.1
                                    have p185_1 := h185c.2.1
                                    have p185_2 := h185c.2.2.1
                                    have p185_3 := h185c.2.2.2
                                    linarith only [hlam, p185_0]
                                · linarith only [h184, hlam, ht01, ht12, u2elo0]
                                · linarith only [h184, h3, hlam, ht01, ht12, u2elo0]
                                · linarith only [h184, h4, hlam, ht01, ht12, u2elo0]
                                · linarith only [h184, h5, hlam, ht01, ht12, u2elo0]
                        · linarith only [h177, h6, h7, hc23, hc35, hlam, hphi]
                  · linarith only [h172, h6, h7, hc13, hc35, hlam, hphi]
                · linarith only [h171, h5, hc12, hlam, hphi, u2elo0]
              · linarith only [h169, h170, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h169, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h222 | h222
        · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
          · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
            · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
              · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
                · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                  · linarith only [h222, h227, h6, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                        · linarith only [h1, h229, h231, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                          · linarith only [h225, h231, h233, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                          · linarith only [h1, h229, h233, h6, hc23, hc34, hlam, hphi]
                      · linarith only [h223, h227, h229, h230, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h222, h229, h6, hc13, hc34, hlam, hphi]
                · linarith only [h226, h5, hc12, hlam, hphi, u2elo0]
              · linarith only [h224, h225, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h224, h3, hc12, hlam, hphi, u2elo0]
          · linarith only [h222, h223, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h242 | h242
          · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
            · rcases m.htr 1 2 4 (by decide) (by decide) with h244 | h244
              · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                  · linarith only [h1, h246, h6, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                    · linarith only [h1, h222, h248, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                        · linarith only [h2, h242, h245, h251, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h253 | h253
                          · linarith only [h1, h222, h243, h253, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h255 | h255
                            · linarith only [h0, h244, h255, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h257 | h257
                              · rcases h0emin with h258 | h258 | h258 | h258 | h258
                                · rcases h3bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h243, h6, hc23, hc34, hlam, hphi, p259_1]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h6, hc23, hc34, hlam, hphi, p259_1]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h6, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h222, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h1, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h1, h6, hc23, hc34, hlam, hphi, p259_1]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h246, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h248, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h3, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h243, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h251, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h253, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    rcases p259_3 (m.d 0 3) (by simp) with h275 | h275
                                    · linarith only [h275, hlam, p259_0]
                                    · rcases p259_3 (m.d 1 3) (by simp) with h277 | h277
                                      · linarith only [h246, h277, hlam]
                                      · rcases p259_3 (m.d 2 3) (by simp) with h279 | h279
                                        · linarith only [h251, h279, hlam]
                                        · rcases p259_3 (m.d 3 4) (by simp) with h281 | h281
                                          · rcases p259_3 (m.d 3 5) (by simp) with h282 | h282
                                            · linarith only [h257, h282, hlam]
                                            · linarith only [h222, h282, hlam]
                                          · linarith only [h281, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    rcases p259_3 (m.d 0 3) (by simp) with h286 | h286
                                    · linarith only [h286, h6, hlam]
                                    · linarith only [h1, h286, hlam]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    rcases p259_3 (m.d 0 3) (by simp) with h289 | h289
                                    · linarith only [h289, h6, hlam]
                                    · linarith only [h289, h3, hlam]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h222, hc03, hc34, hlam, hphi, p259_1]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    rcases p259_3 (m.d 0 3) (by simp) with h294 | h294
                                    · linarith only [h294, hlam, p259_0]
                                    · rcases p259_3 (m.d 1 3) (by simp) with h296 | h296
                                      · linarith only [h248, h296, hlam]
                                      · rcases p259_3 (m.d 2 3) (by simp) with h298 | h298
                                        · linarith only [h253, h298, hlam]
                                        · rcases p259_3 (m.d 3 4) (by simp) with h300 | h300
                                          · rcases p259_3 (m.d 3 5) (by simp) with h301 | h301
                                            · rcases h5bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h250, h251, h255, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u2elo0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p302_1, u2elo0, u5ehi2]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h222, hlam, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h242, h251, h255, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u2elo0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h2, hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p302_1, u5ehi2]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h248, hlam, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h2, h242, h251, h255, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p302_1, u2elo0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h5, hlam, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h245, hlam, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h253, hlam, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h255, hlam, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h242, h251, h255, hc23, hc35, hlam, hphi, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h250, h251, h255, hc23, hc35, hlam, hphi, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                rcases p302_3 (m.d 0 5) (by simp) with h320 | h320
                                                · linarith only [h222, h320, hlam]
                                                · linarith only [h320, h5, hlam]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h251, h255, h257, hc23, hc34, hlam, hphi, p302_1]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h242, hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h250, hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h250, hc14, hlam, hphi, ht01, ht0b, ht5b, p302_1, u5ehi2]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [h257, hlam, p302_0]
                                              · have p302_0 := h302c.1
                                                have p302_1 := h302c.2.1
                                                have p302_2 := h302c.2.2.1
                                                have p302_3 := h302c.2.2.2
                                                linarith only [hlam, p302_0]
                                            · linarith only [h301, hlam, p259_0]
                                          · linarith only [h300, h6, hlam]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    rcases p259_3 (m.d 0 3) (by simp) with h332 | h332
                                    · linarith only [h222, h332, hlam]
                                    · linarith only [h1, h332, hlam]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    rcases p259_3 (m.d 0 3) (by simp) with h335 | h335
                                    · linarith only [h222, h335, hlam]
                                    · linarith only [h3, h335, hlam]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [h257, hlam, p259_0]
                                  · have p259_0 := h259c.1
                                    have p259_1 := h259c.2.1
                                    have p259_2 := h259c.2.2.1
                                    have p259_3 := h259c.2.2.2
                                    linarith only [hlam, p259_0]
                                · linarith only [h258, hlam, ht01, ht12, u2elo0]
                                · linarith only [h258, h3, hlam, ht01, ht12, u2elo0]
                                · linarith only [h258, h4, hlam, ht01, ht12, u2elo0]
                                · linarith only [h242, h258, h4, hlam, ht01, ht12, u2elo0]
                              · linarith only [h0, h244, h250, h257, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                        · linarith only [h242, h250, h345, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                          · linarith only [h242, h243, h246, h250, h347, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h349 | h349
                            · linarith only [h246, h250, h349, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
                              · rcases h0emin with h352 | h352 | h352 | h352 | h352
                                · rcases h3bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h243, h6, hc23, hc34, hlam, hphi, p353_1]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h6, hc23, hc34, hlam, hphi, p353_1]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h6, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h222, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h1, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h242, h246, h250, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p353_1]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h246, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h248, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h3, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h243, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h345, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h347, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    rcases p353_3 (m.d 0 3) (by simp) with h369 | h369
                                    · linarith only [h369, hlam, p353_0]
                                    · rcases p353_3 (m.d 1 3) (by simp) with h371 | h371
                                      · linarith only [h246, h371, hlam]
                                      · rcases p353_3 (m.d 2 3) (by simp) with h373 | h373
                                        · linarith only [h345, h373, hlam]
                                        · rcases p353_3 (m.d 3 4) (by simp) with h375 | h375
                                          · rcases p353_3 (m.d 3 5) (by simp) with h376 | h376
                                            · linarith only [h351, h376, hlam]
                                            · linarith only [h222, h376, hlam]
                                          · linarith only [h375, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    rcases p353_3 (m.d 0 3) (by simp) with h380 | h380
                                    · linarith only [h380, h6, hlam]
                                    · linarith only [h1, h380, hlam]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    rcases p353_3 (m.d 0 3) (by simp) with h383 | h383
                                    · linarith only [h383, h6, hlam]
                                    · linarith only [h3, h383, hlam]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h222, hc03, hc34, hlam, hphi, p353_1]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    rcases p353_3 (m.d 0 3) (by simp) with h388 | h388
                                    · linarith only [h388, hlam, p353_0]
                                    · rcases p353_3 (m.d 1 3) (by simp) with h390 | h390
                                      · linarith only [h248, h390, hlam]
                                      · rcases p353_3 (m.d 2 3) (by simp) with h392 | h392
                                        · linarith only [h347, h392, hlam]
                                        · rcases p353_3 (m.d 3 4) (by simp) with h394 | h394
                                          · rcases p353_3 (m.d 3 5) (by simp) with h395 | h395
                                            · rcases h5bigk with h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c | h396c
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p396_1, u2elo0, u5ehi1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p396_1, u2elo0, u5ehi2]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h222, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, h250, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p396_1, u2elo0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h2, hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p396_1, u5ehi2]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h248, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h250, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h5, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h245, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h347, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h349, hlam, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, h243, h246, h250, hc23, hc35, hlam, hphi, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                rcases p396_3 (m.d 0 5) (by simp) with h413 | h413
                                                · linarith only [h222, h413, hlam]
                                                · linarith only [h2, h413, hlam]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                rcases p396_3 (m.d 0 5) (by simp) with h416 | h416
                                                · linarith only [h222, h416, hlam]
                                                · linarith only [h416, h5, hlam]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h243, h246, h250, h351, hc23, hc34, hlam, hphi, p396_1]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, h245, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p396_1, u2elo0, u5ehi2]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h242, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p396_1, u2elo0, u5ehi2]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [h351, hlam, p396_0]
                                              · have p396_0 := h396c.1
                                                have p396_1 := h396c.2.1
                                                have p396_2 := h396c.2.2.1
                                                have p396_3 := h396c.2.2.2
                                                linarith only [hlam, p396_0]
                                            · linarith only [h395, hlam, p353_0]
                                          · linarith only [h394, h6, hlam]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    rcases p353_3 (m.d 0 3) (by simp) with h428 | h428
                                    · linarith only [h222, h428, hlam]
                                    · linarith only [h1, h428, hlam]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    rcases p353_3 (m.d 0 3) (by simp) with h431 | h431
                                    · linarith only [h222, h431, hlam]
                                    · linarith only [h3, h431, hlam]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [h351, hlam, p353_0]
                                  · have p353_0 := h353c.1
                                    have p353_1 := h353c.2.1
                                    have p353_2 := h353c.2.2.1
                                    have p353_3 := h353c.2.2.2
                                    linarith only [hlam, p353_0]
                                · linarith only [h352, hlam, ht01, ht12, u2elo0]
                                · linarith only [h3, h352, hlam, ht01, ht12, u2elo0]
                                · linarith only [h352, h4, hlam, ht01, ht12, u2elo0]
                                · linarith only [h242, h352, h4, hlam, ht01, ht12, u2elo0]
                              · linarith only [h242, h351, h4, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h245, h5, hc12, hlam, hphi, u2elo0]
              · linarith only [h243, h244, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h243, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
            · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
              · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                  · linarith only [h1, h447, h6, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h449 | h449
                    · linarith only [h1, h222, h449, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h451 | h451
                      · linarith only [h2, h242, h451, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                        · linarith only [h1, h444, h453, h6, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                          · linarith only [h1, h222, h444, h455, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                            · linarith only [h4, h457, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h459 | h459
                              · rcases h0emin with h460 | h460 | h460 | h460 | h460
                                · rcases h3bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h242, h444, h459, h6, hc23, hc34, hlam, hphi, p461_1]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h242, h459, h6, hc23, hc34, hlam, hphi, p461_1]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h6, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h222, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h1, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h1, h242, h459, h6, hc23, hc34, hlam, hphi, p461_1]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h447, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h449, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h3, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h444, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h453, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h455, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    rcases p461_3 (m.d 0 3) (by simp) with h477 | h477
                                    · linarith only [h477, hlam, p461_0]
                                    · rcases p461_3 (m.d 1 3) (by simp) with h479 | h479
                                      · linarith only [h447, h479, hlam]
                                      · rcases p461_3 (m.d 2 3) (by simp) with h481 | h481
                                        · linarith only [h453, h481, hlam]
                                        · rcases p461_3 (m.d 3 4) (by simp) with h483 | h483
                                          · rcases p461_3 (m.d 3 5) (by simp) with h484 | h484
                                            · linarith only [h459, h484, hlam]
                                            · linarith only [h222, h484, hlam]
                                          · linarith only [h483, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    rcases p461_3 (m.d 0 3) (by simp) with h488 | h488
                                    · linarith only [h488, h6, hlam]
                                    · linarith only [h1, h488, hlam]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    rcases p461_3 (m.d 0 3) (by simp) with h491 | h491
                                    · linarith only [h491, h6, hlam]
                                    · linarith only [h3, h491, hlam]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h242, h459, h6, hc03, hc34, hlam, hphi, p461_1]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    rcases p461_3 (m.d 0 3) (by simp) with h496 | h496
                                    · linarith only [h496, hlam, p461_0]
                                    · rcases p461_3 (m.d 1 3) (by simp) with h498 | h498
                                      · linarith only [h449, h498, hlam]
                                      · rcases p461_3 (m.d 2 3) (by simp) with h500 | h500
                                        · linarith only [h455, h500, hlam]
                                        · rcases p461_3 (m.d 3 4) (by simp) with h502 | h502
                                          · rcases p461_3 (m.d 3 5) (by simp) with h503 | h503
                                            · rcases h5bigk with h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [hlam, p504_0]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p504_1, u2elo0, u5ehi1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p504_1, u2elo0, u5ehi2]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h222, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h242, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h2, hlam, p504_0]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [hlam, p504_0]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p504_1, u5ehi2]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h449, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h451, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h5, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h446, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [hlam, p504_0]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h455, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h457, hlam, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                rcases p504_3 (m.d 0 5) (by simp) with h520 | h520
                                                · linarith only [h222, h520, hlam]
                                                · rcases p504_3 (m.d 1 5) (by simp) with h522 | h522
                                                  · linarith only [h449, h522, hlam]
                                                  · rcases p504_3 (m.d 2 5) (by simp) with h524 | h524
                                                    · linarith only [h455, h524, hlam]
                                                    · rcases p504_3 (m.d 3 5) (by simp) with h526 | h526
                                                      · rcases p504_3 (m.d 4 5) (by simp) with h527 | h527
                                                        · linarith only [h459, h527, hlam]
                                                        · linarith only [h242, h527, hlam]
                                                      · linarith only [h222, h526, hlam]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                rcases p504_3 (m.d 0 5) (by simp) with h531 | h531
                                                · linarith only [h222, h531, hlam]
                                                · linarith only [h2, h531, hlam]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                rcases p504_3 (m.d 0 5) (by simp) with h534 | h534
                                                · linarith only [h222, h534, hlam]
                                                · linarith only [h5, h534, hlam]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [hlam, p504_0]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h1, h242, h444, h459, h6, hc23, hc34, hlam, hphi, p504_1]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h2, h446, h459, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p504_1, u5ehi2]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h446, h459, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p504_1, u5ehi2]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h459, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p504_1, u5ehi2]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [h459, hlam, p504_0]
                                              · have p504_0 := h504c.1
                                                have p504_1 := h504c.2.1
                                                have p504_2 := h504c.2.2.1
                                                have p504_3 := h504c.2.2.2
                                                linarith only [hlam, p504_0]
                                            · linarith only [h503, hlam, p461_0]
                                          · linarith only [h502, h6, hlam]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    rcases p461_3 (m.d 0 3) (by simp) with h546 | h546
                                    · linarith only [h222, h546, hlam]
                                    · linarith only [h1, h546, hlam]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    rcases p461_3 (m.d 0 3) (by simp) with h549 | h549
                                    · linarith only [h222, h549, hlam]
                                    · linarith only [h3, h549, hlam]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [h459, hlam, p461_0]
                                  · have p461_0 := h461c.1
                                    have p461_1 := h461c.2.1
                                    have p461_2 := h461c.2.2.1
                                    have p461_3 := h461c.2.2.2
                                    linarith only [hlam, p461_0]
                                · linarith only [h460, hlam, ht01, ht12, u2elo0]
                                · linarith only [h3, h460, hlam, ht01, ht12, u2elo0]
                                · linarith only [h4, h460, hlam, ht01, ht12, u2elo0]
                                · linarith only [h460, h5, hlam, ht01, ht12, u2elo0]
                              · rcases h0emin with h558 | h558 | h558 | h558 | h558
                                · rcases h3bigk with h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h444, h459, h6, hc23, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h459, h6, hc23, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h6, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h222, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h1, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h1, h459, h6, hc23, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h447, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h449, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h3, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h444, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h453, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h455, hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h459, hc03, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h459, hc13, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h459, hc23, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [hlam, p559_0]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h459, hlam, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    rcases p559_3 (m.d 0 3) (by simp) with h580 | h580
                                    · linarith only [h580, hlam, p559_0]
                                    · rcases p559_3 (m.d 1 3) (by simp) with h582 | h582
                                      · linarith only [h449, h582, hlam]
                                      · rcases p559_3 (m.d 2 3) (by simp) with h584 | h584
                                        · linarith only [h455, h584, hlam]
                                        · rcases p559_3 (m.d 3 4) (by simp) with h586 | h586
                                          · linarith only [h459, h586, hlam]
                                          · linarith only [h586, h6, hlam]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    rcases p559_3 (m.d 0 3) (by simp) with h589 | h589
                                    · linarith only [h222, h589, hlam]
                                    · linarith only [h1, h589, hlam]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    rcases p559_3 (m.d 0 3) (by simp) with h592 | h592
                                    · linarith only [h222, h592, hlam]
                                    · linarith only [h3, h592, hlam]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [h459, h6, hc03, hc45, hlam, hphi, ht34, p559_1]
                                  · have p559_0 := h559c.1
                                    have p559_1 := h559c.2.1
                                    have p559_2 := h559c.2.2.1
                                    have p559_3 := h559c.2.2.2
                                    linarith only [hlam, p559_0]
                                · linarith only [h558, hlam, ht01, ht12, u2elo0]
                                · linarith only [h558, h6, hc34, hlam, ht01, ht12, ht23]
                                · linarith only [h4, h558, hlam, ht01, ht12, u2elo0]
                                · linarith only [h5, h558, hlam, ht01, ht12, u2elo0]
                · linarith only [h446, h5, hc12, hlam, hphi, u2elo0]
              · linarith only [h4, h444, h445, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h3, h444, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h604 | h604
      · rcases m.htr 0 3 5 (by decide) (by decide) with h605 | h605
        · linarith only [h3, h5, h605, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h607 | h607
          · linarith only [h3, h5, h604, h607, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h609 | h609
            · rcases m.htr 1 2 4 (by decide) (by decide) with h610 | h610
              · rcases m.htr 1 2 5 (by decide) (by decide) with h611 | h611
                · linarith only [h5, h611, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h614 | h614
                    · linarith only [h1, h2, h3, h5, h605, h614, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h616 | h616
                      · linarith only [h1, h3, h5, h607, h613, h616, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h618 | h618
                        · linarith only [h0, h5, h609, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · linarith only [h3, h5, h604, h618, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h3, h5, h604, h613, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h4, h5, h610, hc12, hlam, hphi, u2elo4]
            · linarith only [h3, h5, h609, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h624 | h624
        · linarith only [h4, h5, h604, h624, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h626 | h626
          · linarith only [h4, h5, h626, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
            · rcases m.htr 1 2 4 (by decide) (by decide) with h629 | h629
              · rcases m.htr 1 2 5 (by decide) (by decide) with h630 | h630
                · linarith only [h5, h630, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
                  · linarith only [h1, h604, h632, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
                    · linarith only [h1, h624, h634, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                      · linarith only [h0, h1, h5, h604, h626, h629, h636, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h638 | h638
                        · linarith only [h3, h5, h632, h638, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h640 | h640
                          · linarith only [h0, h5, h624, h629, h638, h640, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                            · linarith only [h4, h5, h626, h642, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h644 | h644
                              · linarith only [h3, h5, h642, h644, hc23, hc34, hlam, hphi]
                              · rcases h0emin with h646 | h646 | h646 | h646 | h646
                                · rcases h3bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h3, h5, h628, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p647_1, u2elo4]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p647_1, u2elo4]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h604, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h624, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h1, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h1, h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p647_1, u2elo4]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h632, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h634, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h3, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h628, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h638, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h640, hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h644, hc03, hc45, hlam, hphi, ht34, p647_1]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h628, h644, hc23, hc45, hlam, hphi, ht34, p647_1]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h644, hc23, hc45, hlam, hphi, ht34, p647_1]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [hlam, p647_0]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h644, hlam, p647_1]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    rcases p647_3 (m.d 0 3) (by simp) with h668 | h668
                                    · linarith only [h668, hlam, p647_0]
                                    · rcases p647_3 (m.d 1 3) (by simp) with h670 | h670
                                      · linarith only [h634, h670, hlam]
                                      · rcases p647_3 (m.d 2 3) (by simp) with h672 | h672
                                        · linarith only [h640, h672, hlam]
                                        · rcases p647_3 (m.d 3 4) (by simp) with h674 | h674
                                          · linarith only [h644, h674, hlam]
                                          · linarith only [h604, h674, hlam]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    rcases p647_3 (m.d 0 3) (by simp) with h677 | h677
                                    · linarith only [h624, h677, hlam]
                                    · linarith only [h1, h677, hlam]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    rcases p647_3 (m.d 0 3) (by simp) with h680 | h680
                                    · linarith only [h624, h680, hlam]
                                    · linarith only [h3, h680, hlam]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [h1, h604, h628, hc23, hc35, hlam, hphi, p647_1]
                                  · have p647_0 := h647c.1
                                    have p647_1 := h647c.2.1
                                    have p647_2 := h647c.2.2.1
                                    have p647_3 := h647c.2.2.2
                                    linarith only [hlam, p647_0]
                                · linarith only [h5, h646, hlam, ht01, ht12, u2elo4]
                                · linarith only [h0, h5, h604, h629, h638, h646, hc23, hc34, hlam, hphi, ht01, ht12, u2elo4]
                                · linarith only [h4, h5, h646, hlam, ht01, ht12, u2elo4]
                                · linarith only [h5, h646, hlam, ht01, ht12, u2elo4]
              · linarith only [h4, h5, h629, hc12, hlam, hphi, u2elo4]
            · linarith only [h3, h5, h628, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h691 | h691
    · linarith only [h4, h691, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h693 | h693
      · linarith only [h3, h4, h693, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h695 | h695
        · linarith only [h3, h4, h695, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h697 | h697
          · rcases m.htr 1 2 3 (by decide) (by decide) with h698 | h698
            · rcases m.htr 1 2 4 (by decide) (by decide) with h699 | h699
              · linarith only [h0, h4, h699, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
                · linarith only [h0, h691, h701, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h703 | h703
                  · linarith only [h1, h3, h4, h693, h697, h703, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h705 | h705
                    · linarith only [h1, h695, h705, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h707 | h707
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h708 | h708
                        · linarith only [h0, h4, h693, h698, h708, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h710 | h710
                          · linarith only [h3, h691, h695, h710, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h712 | h712
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h713 | h713
                              · rcases h0emin with h714 | h714 | h714 | h714 | h714
                                · rcases h3bigk with h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h3, h691, h698, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p715_1, u2elo4]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h3, h691, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p715_1, u2elo4]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h693, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h695, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h1, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h1, h3, h691, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p715_1, u2elo4]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h703, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h705, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h3, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h698, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h708, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h710, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    rcases p715_3 (m.d 0 3) (by simp) with h731 | h731
                                    · linarith only [h731, hlam, p715_0]
                                    · rcases p715_3 (m.d 1 3) (by simp) with h733 | h733
                                      · linarith only [h703, h733, hlam]
                                      · rcases p715_3 (m.d 2 3) (by simp) with h735 | h735
                                        · linarith only [h708, h735, hlam]
                                        · rcases p715_3 (m.d 3 4) (by simp) with h737 | h737
                                          · rcases p715_3 (m.d 3 5) (by simp) with h738 | h738
                                            · linarith only [h713, h738, hlam]
                                            · linarith only [h695, h738, hlam]
                                          · linarith only [h737, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    rcases p715_3 (m.d 0 3) (by simp) with h742 | h742
                                    · linarith only [h693, h742, hlam]
                                    · linarith only [h1, h742, hlam]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    rcases p715_3 (m.d 0 3) (by simp) with h745 | h745
                                    · linarith only [h693, h745, hlam]
                                    · linarith only [h3, h745, hlam]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h691, h710, hc02, hc34, hlam, hphi, ht23, p715_1]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    rcases p715_3 (m.d 0 3) (by simp) with h750 | h750
                                    · linarith only [h750, hlam, p715_0]
                                    · rcases p715_3 (m.d 1 3) (by simp) with h752 | h752
                                      · linarith only [h705, h752, hlam]
                                      · rcases p715_3 (m.d 2 3) (by simp) with h754 | h754
                                        · linarith only [h710, h754, hlam]
                                        · rcases p715_3 (m.d 3 4) (by simp) with h756 | h756
                                          · rcases p715_3 (m.d 3 5) (by simp) with h757 | h757
                                            · rcases h5bigk with h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h4, h697, h698, h701, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p758_1, u2elo3]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h691, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h695, hlam, p758_1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h4, h697, hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo3, u5ehi4]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h2, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h701, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h705, hlam, p758_1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p758_1, u5ehi4]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo4, u5ehi0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo4, u5ehi1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h710, hlam, p758_1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h712, hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo3, u5ehi4]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h2, h698, h701, h713, hc23, hc34, hlam, hphi, p758_1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h698, h701, h713, hc23, hc34, hlam, hphi, p758_1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h0, h691, h698, h713, hc23, hc34, hlam, hphi, p758_1]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                rcases p758_3 (m.d 0 5) (by simp) with h778 | h778
                                                · linarith only [h695, h778, hlam]
                                                · linarith only [h697, h778, hlam]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h697, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h707, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h712, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [h713, hlam, p758_0]
                                              · have p758_0 := h758c.1
                                                have p758_1 := h758c.2.1
                                                have p758_2 := h758c.2.2.1
                                                have p758_3 := h758c.2.2.2
                                                linarith only [hlam, p758_0]
                                            · linarith only [h757, hlam, p715_0]
                                          · linarith only [h693, h756, hlam]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    rcases p715_3 (m.d 0 3) (by simp) with h788 | h788
                                    · linarith only [h695, h788, hlam]
                                    · linarith only [h1, h788, hlam]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    rcases p715_3 (m.d 0 3) (by simp) with h791 | h791
                                    · linarith only [h695, h791, hlam]
                                    · linarith only [h3, h791, hlam]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [h713, hlam, p715_0]
                                  · have p715_0 := h715c.1
                                    have p715_1 := h715c.2.1
                                    have p715_2 := h715c.2.2.1
                                    have p715_3 := h715c.2.2.2
                                    linarith only [hlam, p715_0]
                                · linarith only [h691, h714, hlam, ht01, ht12, u2elo4]
                                · linarith only [h3, h691, h714, hlam, ht01, ht12, u2elo4]
                                · linarith only [h4, h714, hlam, ht01, ht12, u2elo3]
                                · linarith only [h691, h714, hlam, ht01, ht12, u2elo4]
                              · linarith only [h693, h697, h713, hlam]
                            · linarith only [h0, h4, h697, h698, h712, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h4, h697, h698, h699, h707, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h3, h698, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
            · rcases m.htr 1 2 4 (by decide) (by decide) with h805 | h805
              · linarith only [h4, h805, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
                · linarith only [h0, h4, h807, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
                  · linarith only [h1, h693, h809, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h811 | h811
                    · linarith only [h1, h3, h4, h811, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h813 | h813
                      · linarith only [h4, h697, h805, h813, hc02, hlam, hphi, u2elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
                        · linarith only [h0, h1, h691, h693, h804, h815, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h817 | h817
                          · linarith only [h3, h4, h695, h697, h817, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h819 | h819
                            · linarith only [h4, h697, h819, hc02, hlam, hphi, u2elo3]
                            · linarith only [h0, h4, h804, h819, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h3, h4, h804, hc12, hlam, hphi, u2elo3]

end R2N4
