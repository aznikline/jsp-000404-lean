import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
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
                        · linarith only [h15, h16, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h19, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h1, h12, h15, h21, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h1, h12, h15, h21, h23, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · linarith only [h15, h23, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h27, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · linarith only [h13, h14, h26, h27, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h12, h14, h26, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h12, h13, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                      · linarith only [h12, h32, h34, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h0, h10, h34, h36, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · linarith only [h12, h32, h36, hc23, hc34, hlam, hphi]
                    · linarith only [h12, h32, h33, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                      · linarith only [h32, h4, h41, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                        · linarith only [h32, h43, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                          · linarith only [h0, h10, h45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                            · rcases h1bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h10, h40, h41, h45, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                rcases p48_3 (m.d 0 1) (by simp) with h51 | h51
                                · rcases p48_3 (m.d 1 2) (by simp) with h52 | h52
                                  · linarith only [h0, h52, hlam]
                                  · linarith only [h52, h9, hlam]
                                · linarith only [h51, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h40, h41, h45, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                rcases p48_3 (m.d 0 1) (by simp) with h57 | h57
                                · rcases p48_3 (m.d 1 2) (by simp) with h58 | h58
                                  · linarith only [h0, h58, hlam]
                                  · linarith only [h11, h58, hlam]
                                · linarith only [h57, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                rcases p48_3 (m.d 0 1) (by simp) with h64 | h64
                                · rcases p48_3 (m.d 1 2) (by simp) with h65 | h65
                                  · rcases p48_3 (m.d 1 3) (by simp) with h66 | h66
                                    · linarith only [h66, h9, hlam]
                                    · rcases p48_3 (m.d 1 4) (by simp) with h68 | h68
                                      · linarith only [h10, h68, hlam]
                                      · linarith only [h12, h68, hlam]
                                  · linarith only [h65, h9, hlam]
                                · linarith only [h1, h64, hlam]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h40, h41, h45, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p48_1, u2elo0, u5ehi1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h1, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h9, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h12, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h32, hlam, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h2, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h10, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                rcases p48_3 (m.d 0 1) (by simp) with h82 | h82
                                · rcases p48_3 (m.d 1 2) (by simp) with h83 | h83
                                  · rcases p48_3 (m.d 1 3) (by simp) with h84 | h84
                                    · linarith only [h12, h84, hlam]
                                    · rcases p48_3 (m.d 1 4) (by simp) with h86 | h86
                                      · rcases p48_3 (m.d 1 5) (by simp) with h87 | h87
                                        · linarith only [h40, h87, hlam]
                                        · linarith only [h32, h87, hlam]
                                      · linarith only [h12, h86, hlam]
                                  · linarith only [h83, h9, hlam]
                                · linarith only [h1, h82, hlam]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h12, h40, h41, h45, hc23, hc34, hlam, hphi, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h3, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h11, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h32, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p48_1, u2elo0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h40, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                            · linarith only [h12, h47, h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                      · linarith only [h101, h12, h9, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                        · linarith only [h103, h32, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                          · linarith only [h105, h12, h40, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                            · rcases h1bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h11, hc01, hlam, hphi, ht0b, ht5b, p108_1, u5ehi2]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 1) (by simp) with h111 | h111
                                · rcases p108_3 (m.d 1 2) (by simp) with h112 | h112
                                  · linarith only [h0, h112, hlam]
                                  · linarith only [h112, h9, hlam]
                                · linarith only [h111, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 1) (by simp) with h116 | h116
                                · rcases p108_3 (m.d 1 2) (by simp) with h117 | h117
                                  · linarith only [h0, h117, hlam]
                                  · linarith only [h10, h117, hlam]
                                · linarith only [h116, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 1) (by simp) with h121 | h121
                                · rcases p108_3 (m.d 1 2) (by simp) with h122 | h122
                                  · linarith only [h0, h122, hlam]
                                  · linarith only [h11, h122, hlam]
                                · linarith only [h121, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h0, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 1) (by simp) with h128 | h128
                                · rcases p108_3 (m.d 1 2) (by simp) with h129 | h129
                                  · rcases p108_3 (m.d 1 3) (by simp) with h130 | h130
                                    · linarith only [h130, h9, hlam]
                                    · rcases p108_3 (m.d 1 4) (by simp) with h132 | h132
                                      · linarith only [h10, h132, hlam]
                                      · linarith only [h12, h132, hlam]
                                  · linarith only [h129, h9, hlam]
                                · linarith only [h1, h128, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                rcases p108_3 (m.d 0 1) (by simp) with h137 | h137
                                · rcases p108_3 (m.d 1 2) (by simp) with h138 | h138
                                  · rcases p108_3 (m.d 1 3) (by simp) with h139 | h139
                                    · linarith only [h139, h9, hlam]
                                    · rcases p108_3 (m.d 1 4) (by simp) with h141 | h141
                                      · linarith only [h10, h141, hlam]
                                      · rcases p108_3 (m.d 1 5) (by simp) with h143 | h143
                                        · linarith only [h11, h143, hlam]
                                        · linarith only [h143, h40, hlam]
                                  · linarith only [h10, h138, hlam]
                                · linarith only [h137, h2, hlam]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, p108_1, u5ehi2]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h1, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h9, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h12, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h32, hlam, p108_1]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h2, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h10, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h107, h40, h9, hc23, hc34, hlam, hphi, p108_1]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h40, hlam, p108_1]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h3, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h11, hlam, p108_0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h32, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p108_1, u2elo0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [h107, h4, h40, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p108_1, u2elo0]
                              · have p108_0 := h108c.1
                                have p108_1 := h108c.2.1
                                have p108_2 := h108c.2.2.1
                                have p108_3 := h108c.2.2.2
                                linarith only [hlam, p108_0]
                            · linarith only [h107, h12, h5, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h11, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h10, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
          · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h173, h2, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                        · linarith only [h168, h176, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                        · linarith only [h1, h172, h175, h176, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                        · linarith only [h171, h175, h179, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                          · linarith only [h1, h171, h175, h181, h4, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                            · linarith only [h171, h183, h2, h8, hlam]
                            · rcases h1bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h168, h172, h175, h183, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h172, h175, h183, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                rcases p185_3 (m.d 0 1) (by simp) with h189 | h189
                                · rcases p185_3 (m.d 1 2) (by simp) with h190 | h190
                                  · linarith only [h0, h190, hlam]
                                  · linarith only [h169, h190, hlam]
                                · linarith only [h189, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                rcases p185_3 (m.d 0 1) (by simp) with h194 | h194
                                · rcases p185_3 (m.d 1 2) (by simp) with h195 | h195
                                  · linarith only [h0, h195, hlam]
                                  · linarith only [h170, h195, hlam]
                                · linarith only [h194, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h0, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h172, h175, h183, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h0, h171, h175, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p185_1, u2elo0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p185_1, u2elo0, u5ehi1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h1, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h168, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h1, h171, h175, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p185_1, u2elo0, u5ehi1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h2, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h169, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h171, hlam, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h173, hlam, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h3, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h170, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h172, hlam, p185_0]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [h171, h175, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p185_1]
                              · have p185_0 := h185c.1
                                have p185_1 := h185c.2.1
                                have p185_2 := h185c.2.2.1
                                have p185_3 := h185c.2.2.2
                                linarith only [hlam, p185_0]
                  · linarith only [h171, h172, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                    · linarith only [h2, h221, h8, hlam]
                    · linarith only [h171, h220, h221, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                    · linarith only [h2, h224, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                      · linarith only [h168, h171, h226, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                        · linarith only [h168, h220, h228, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                          · linarith only [h230, h5, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                            · linarith only [h232, h7, h8, hlam]
                            · rcases h1bigk with h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c | h234c
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h170, hc01, hlam, hphi, ht0b, ht5b, p234_1, u5ehi2]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                rcases p234_3 (m.d 0 1) (by simp) with h237 | h237
                                · rcases p234_3 (m.d 1 2) (by simp) with h238 | h238
                                  · linarith only [h0, h238, hlam]
                                  · linarith only [h168, h238, hlam]
                                · linarith only [h237, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                rcases p234_3 (m.d 0 1) (by simp) with h242 | h242
                                · rcases p234_3 (m.d 1 2) (by simp) with h243 | h243
                                  · linarith only [h0, h243, hlam]
                                  · linarith only [h169, h243, hlam]
                                · linarith only [h242, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                rcases p234_3 (m.d 0 1) (by simp) with h247 | h247
                                · rcases p234_3 (m.d 1 2) (by simp) with h248 | h248
                                  · linarith only [h0, h248, hlam]
                                  · linarith only [h170, h248, hlam]
                                · linarith only [h247, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h0, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                rcases p234_3 (m.d 0 1) (by simp) with h254 | h254
                                · rcases p234_3 (m.d 1 2) (by simp) with h255 | h255
                                  · rcases p234_3 (m.d 1 3) (by simp) with h256 | h256
                                    · linarith only [h168, h256, hlam]
                                    · rcases p234_3 (m.d 1 4) (by simp) with h258 | h258
                                      · linarith only [h169, h258, hlam]
                                      · linarith only [h171, h258, hlam]
                                  · linarith only [h168, h255, hlam]
                                · linarith only [h1, h254, hlam]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                rcases p234_3 (m.d 0 1) (by simp) with h263 | h263
                                · rcases p234_3 (m.d 1 2) (by simp) with h264 | h264
                                  · rcases p234_3 (m.d 1 3) (by simp) with h265 | h265
                                    · linarith only [h168, h265, hlam]
                                    · rcases p234_3 (m.d 1 4) (by simp) with h267 | h267
                                      · linarith only [h169, h267, hlam]
                                      · rcases p234_3 (m.d 1 5) (by simp) with h269 | h269
                                        · linarith only [h170, h269, hlam]
                                        · linarith only [h224, h269, hlam]
                                  · linarith only [h169, h264, hlam]
                                · linarith only [h2, h263, hlam]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p234_1, u5ehi1]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h1, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h168, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h171, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h220, hlam, p234_1]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h2, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h169, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h168, h2, h8, hc23, hc45, hlam, hphi, ht34, p234_1]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h224, hlam, p234_1]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h3, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h170, hlam, p234_0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h168, h220, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p234_1, u2elo0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [h220, h4, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p234_1, u2elo0]
                              · have p234_0 := h234c.1
                                have p234_1 := h234c.2.1
                                have p234_2 := h234c.2.2.1
                                have p234_3 := h234c.2.2.2
                                linarith only [hlam, p234_0]
              · linarith only [h170, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h168, h169, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h168, h4, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
        · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
          · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
            · rcases m.htr 1 2 5 (by decide) (by decide) with h296 | h296
              · rcases m.htr 1 3 4 (by decide) (by decide) with h297 | h297
                · rcases m.htr 1 3 5 (by decide) (by decide) with h298 | h298
                  · linarith only [h1, h298, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h300 | h300
                    · linarith only [h297, h298, h300, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                        · linarith only [h294, h303, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h295, h300, h305, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                            · linarith only [h297, h298, h300, h307, hlam]
                            · linarith only [h1, h293, h294, h302, h307, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h1, h297, h302, h7, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h311 | h311
                  · linarith only [h1, h311, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
                      · linarith only [h297, h314, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                        · linarith only [h316, h4, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                          · linarith only [h318, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                            · rcases h1bigk with h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h295, h313, h314, h318, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                rcases p321_3 (m.d 0 1) (by simp) with h324 | h324
                                · rcases p321_3 (m.d 1 2) (by simp) with h325 | h325
                                  · linarith only [h0, h325, hlam]
                                  · linarith only [h294, h325, hlam]
                                · linarith only [h324, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h313, h314, h318, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p321_1]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                rcases p321_3 (m.d 0 1) (by simp) with h330 | h330
                                · rcases p321_3 (m.d 1 2) (by simp) with h331 | h331
                                  · linarith only [h0, h331, hlam]
                                  · linarith only [h296, h331, hlam]
                                · linarith only [h330, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h0, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                rcases p321_3 (m.d 0 1) (by simp) with h337 | h337
                                · rcases p321_3 (m.d 1 2) (by simp) with h338 | h338
                                  · rcases p321_3 (m.d 1 3) (by simp) with h339 | h339
                                    · linarith only [h294, h339, hlam]
                                    · rcases p321_3 (m.d 1 4) (by simp) with h341 | h341
                                      · linarith only [h295, h341, hlam]
                                      · linarith only [h297, h341, hlam]
                                  · linarith only [h294, h338, hlam]
                                · linarith only [h1, h337, hlam]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h0, h313, h314, h318, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p321_1, u2elo0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h0, h313, h314, h318, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p321_1, u2elo0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h1, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h294, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h297, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h311, hlam, p321_1]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h2, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h295, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                rcases p321_3 (m.d 0 1) (by simp) with h355 | h355
                                · rcases p321_3 (m.d 1 2) (by simp) with h356 | h356
                                  · rcases p321_3 (m.d 1 3) (by simp) with h357 | h357
                                    · linarith only [h297, h357, hlam]
                                    · rcases p321_3 (m.d 1 4) (by simp) with h359 | h359
                                      · rcases p321_3 (m.d 1 5) (by simp) with h360 | h360
                                        · linarith only [h313, h360, hlam]
                                        · linarith only [h311, h360, hlam]
                                      · linarith only [h297, h359, hlam]
                                  · linarith only [h294, h356, hlam]
                                · linarith only [h1, h355, hlam]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h2, h313, h314, h318, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p321_1, u2elo0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h3, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h296, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                rcases p321_3 (m.d 0 1) (by simp) with h370 | h370
                                · rcases p321_3 (m.d 1 2) (by simp) with h371 | h371
                                  · rcases p321_3 (m.d 1 3) (by simp) with h372 | h372
                                    · linarith only [h311, h372, hlam]
                                    · rcases p321_3 (m.d 1 4) (by simp) with h374 | h374
                                      · rcases p321_3 (m.d 1 5) (by simp) with h375 | h375
                                        · rcases h1emin with h376 | h376 | h376 | h376 | h376
                                          · rcases h5bigk with h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c | h377c
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p321_1, p377_1, u2elo0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p377_1, u2elo0, u5ehi2]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h7, hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, h314, h318, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p377_1, u2elo0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h3, hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p377_1, u5ehi2]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h311, hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, h3, h314, h318, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p377_1, u2elo0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h6, hlam, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h296, hlam, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h316, hlam, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h318, hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, h314, h318, h320, hc23, hc34, hlam, hphi, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h294, h320, hc23, hc34, hlam, hphi, p321_1, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              rcases p377_3 (m.d 0 5) (by simp) with h395 | h395
                                              · linarith only [h395, h7, hlam]
                                              · linarith only [h395, h6, hlam]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [hlam, p377_0]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h314, h318, h320, hc23, hc34, hlam, hphi, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, hlam, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h313, hlam, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h293, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p377_1, u2elo0, u5ehi2]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [h320, hlam, p377_1]
                                            · have p377_0 := h377c.1
                                              have p377_1 := h377c.2.1
                                              have p377_2 := h377c.2.2.1
                                              have p377_3 := h377c.2.2.2
                                              linarith only [hlam, p377_0]
                                          · linarith only [h0, h376, hlam, ht12, u2elo0]
                                          · linarith only [h3, h376, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p321_1]
                                          · linarith only [h2, h376, h5, hlam, ht12, u2elo0]
                                          · linarith only [h3, h376, h6, hlam, ht12, u2elo0]
                                        · linarith only [h311, h375, hlam]
                                      · linarith only [h297, h374, hlam]
                                  · linarith only [h294, h371, hlam]
                                · linarith only [h1, h370, hlam]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [h313, hlam, p321_0]
                              · have p321_0 := h321c.1
                                have p321_1 := h321c.2.1
                                have p321_2 := h321c.2.2.1
                                have p321_3 := h321c.2.2.2
                                linarith only [hlam, p321_0]
                            · linarith only [h2, h294, h297, h313, h320, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                      · linarith only [h294, h297, h416, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h418 | h418
                        · linarith only [h4, h418, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h420 | h420
                          · linarith only [h294, h297, h313, h420, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                            · rcases h1bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h296, hc01, hlam, hphi, ht0b, ht5b, p423_1, u5ehi2]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h426 | h426
                                · rcases p423_3 (m.d 1 2) (by simp) with h427 | h427
                                  · linarith only [h0, h427, hlam]
                                  · linarith only [h294, h427, hlam]
                                · linarith only [h426, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h431 | h431
                                · rcases p423_3 (m.d 1 2) (by simp) with h432 | h432
                                  · linarith only [h0, h432, hlam]
                                  · linarith only [h295, h432, hlam]
                                · linarith only [h431, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h436 | h436
                                · rcases p423_3 (m.d 1 2) (by simp) with h437 | h437
                                  · linarith only [h0, h437, hlam]
                                  · linarith only [h296, h437, hlam]
                                · linarith only [h436, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h0, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h443 | h443
                                · rcases p423_3 (m.d 1 2) (by simp) with h444 | h444
                                  · rcases p423_3 (m.d 1 3) (by simp) with h445 | h445
                                    · linarith only [h294, h445, hlam]
                                    · rcases p423_3 (m.d 1 4) (by simp) with h447 | h447
                                      · linarith only [h295, h447, hlam]
                                      · linarith only [h297, h447, hlam]
                                  · linarith only [h294, h444, hlam]
                                · linarith only [h1, h443, hlam]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h452 | h452
                                · rcases p423_3 (m.d 1 2) (by simp) with h453 | h453
                                  · rcases p423_3 (m.d 1 3) (by simp) with h454 | h454
                                    · linarith only [h294, h454, hlam]
                                    · rcases p423_3 (m.d 1 4) (by simp) with h456 | h456
                                      · linarith only [h295, h456, hlam]
                                      · rcases p423_3 (m.d 1 5) (by simp) with h458 | h458
                                        · linarith only [h296, h458, hlam]
                                        · linarith only [h313, h458, hlam]
                                  · linarith only [h295, h453, hlam]
                                · linarith only [h2, h452, hlam]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p423_1, u5ehi1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h1, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h294, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h297, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h311, hlam, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h2, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h295, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h293, h294, h313, h7, hc23, hc35, hlam, hphi, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h313, hlam, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h3, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h296, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h293, h294, h313, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p423_1, u2elo0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h293, h313, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p423_1, u2elo0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                            · linarith only [h293, h294, h297, h422, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h296, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h294, h295, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h294, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
          · rcases m.htr 1 2 4 (by decide) (by decide) with h484 | h484
            · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
              · rcases m.htr 1 3 4 (by decide) (by decide) with h486 | h486
                · rcases m.htr 1 3 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h1, h487, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h2, h293, h489, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h492 | h492
                        · linarith only [h0, h483, h492, h7, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                          · linarith only [h293, h3, h484, h486, h487, h494, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h0, h293, h485, h491, h492, h496, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases h1bigk with h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h485, hc01, hlam, hphi, ht0b, ht5b, p498_1, u5ehi2]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                rcases p498_3 (m.d 0 1) (by simp) with h501 | h501
                                · rcases p498_3 (m.d 1 2) (by simp) with h502 | h502
                                  · linarith only [h0, h502, hlam]
                                  · linarith only [h483, h502, hlam]
                                · linarith only [h501, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                rcases p498_3 (m.d 0 1) (by simp) with h506 | h506
                                · rcases p498_3 (m.d 1 2) (by simp) with h507 | h507
                                  · linarith only [h0, h507, hlam]
                                  · linarith only [h484, h507, hlam]
                                · linarith only [h506, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                rcases p498_3 (m.d 0 1) (by simp) with h511 | h511
                                · rcases p498_3 (m.d 1 2) (by simp) with h512 | h512
                                  · linarith only [h0, h512, hlam]
                                  · linarith only [h485, h512, hlam]
                                · linarith only [h511, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h0, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h0, h483, h491, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p498_1, u2elo0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                rcases p498_3 (m.d 0 1) (by simp) with h519 | h519
                                · rcases p498_3 (m.d 1 2) (by simp) with h520 | h520
                                  · rcases p498_3 (m.d 1 3) (by simp) with h521 | h521
                                    · linarith only [h483, h521, hlam]
                                    · linarith only [h486, h521, hlam]
                                  · linarith only [h484, h520, hlam]
                                · linarith only [h2, h519, hlam]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p498_1, u2elo0, u5ehi1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h1, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h483, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h1, h484, h491, h496, h7, hc34, hc45, hlam, hphi, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h487, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h2, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h484, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h486, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h489, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h3, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h485, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h3, h483, h491, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                rcases p498_3 (m.d 0 1) (by simp) with h540 | h540
                                · rcases p498_3 (m.d 1 2) (by simp) with h541 | h541
                                  · rcases p498_3 (m.d 1 3) (by simp) with h542 | h542
                                    · linarith only [h487, h542, hlam]
                                    · linarith only [h486, h542, hlam]
                                  · linarith only [h484, h541, hlam]
                                · linarith only [h2, h540, hlam]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                      · linarith only [h1, h486, h491, h7, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                  · linarith only [h486, h549, h7, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                    · linarith only [h2, h293, h551, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                      · linarith only [h483, h486, h553, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                        · linarith only [h3, h4, h555, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                          · linarith only [h0, h293, h484, h557, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                            · rcases h1bigk with h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c | h560c
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h485, hc01, hlam, hphi, ht0b, ht5b, p560_1, u5ehi2]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                rcases p560_3 (m.d 0 1) (by simp) with h563 | h563
                                · rcases p560_3 (m.d 1 2) (by simp) with h564 | h564
                                  · linarith only [h0, h564, hlam]
                                  · linarith only [h483, h564, hlam]
                                · linarith only [h563, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                rcases p560_3 (m.d 0 1) (by simp) with h568 | h568
                                · rcases p560_3 (m.d 1 2) (by simp) with h569 | h569
                                  · linarith only [h0, h569, hlam]
                                  · linarith only [h484, h569, hlam]
                                · linarith only [h568, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                rcases p560_3 (m.d 0 1) (by simp) with h573 | h573
                                · rcases p560_3 (m.d 1 2) (by simp) with h574 | h574
                                  · linarith only [h0, h574, hlam]
                                  · linarith only [h485, h574, hlam]
                                · linarith only [h573, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h0, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                rcases p560_3 (m.d 0 1) (by simp) with h580 | h580
                                · rcases p560_3 (m.d 1 2) (by simp) with h581 | h581
                                  · rcases p560_3 (m.d 1 3) (by simp) with h582 | h582
                                    · linarith only [h483, h582, hlam]
                                    · rcases p560_3 (m.d 1 4) (by simp) with h584 | h584
                                      · linarith only [h484, h584, hlam]
                                      · linarith only [h486, h584, hlam]
                                  · linarith only [h483, h581, hlam]
                                · linarith only [h1, h580, hlam]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                rcases p560_3 (m.d 0 1) (by simp) with h589 | h589
                                · rcases p560_3 (m.d 1 2) (by simp) with h590 | h590
                                  · rcases p560_3 (m.d 1 3) (by simp) with h591 | h591
                                    · linarith only [h483, h591, hlam]
                                    · rcases p560_3 (m.d 1 4) (by simp) with h593 | h593
                                      · linarith only [h484, h593, hlam]
                                      · rcases p560_3 (m.d 1 5) (by simp) with h595 | h595
                                        · linarith only [h485, h595, hlam]
                                        · linarith only [h551, h595, hlam]
                                  · linarith only [h484, h590, hlam]
                                · linarith only [h2, h589, hlam]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h0, h485, hlam, hphi, ht01, ht0b, ht12, ht5b, p560_1, u2elo0, u5ehi2]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h1, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h483, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h486, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h549, hlam, p560_1]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h2, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h484, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h2, h293, h483, h559, hc23, hc34, hlam, hphi, p560_1]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h551, hlam, p560_1]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h3, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h485, hlam, p560_0]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h293, h3, h483, h559, hc23, hc34, hlam, hphi, p560_1]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [h293, h3, h484, h553, h559, hc23, hc34, hlam, hphi, p560_1]
                              · have p560_0 := h560c.1
                                have p560_1 := h560c.2.1
                                have p560_2 := h560c.2.2.1
                                have p560_3 := h560c.2.2.2
                                linarith only [hlam, p560_0]
                            · rcases h1bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h485, hc01, hlam, hphi, ht0b, ht5b, p616_1, u5ehi2]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h619 | h619
                                · rcases p616_3 (m.d 1 2) (by simp) with h620 | h620
                                  · linarith only [h0, h620, hlam]
                                  · linarith only [h483, h620, hlam]
                                · linarith only [h619, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h624 | h624
                                · rcases p616_3 (m.d 1 2) (by simp) with h625 | h625
                                  · linarith only [h0, h625, hlam]
                                  · linarith only [h484, h625, hlam]
                                · linarith only [h624, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h629 | h629
                                · rcases p616_3 (m.d 1 2) (by simp) with h630 | h630
                                  · linarith only [h0, h630, hlam]
                                  · linarith only [h485, h630, hlam]
                                · linarith only [h629, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h0, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h636 | h636
                                · rcases p616_3 (m.d 1 2) (by simp) with h637 | h637
                                  · rcases p616_3 (m.d 1 3) (by simp) with h638 | h638
                                    · linarith only [h483, h638, hlam]
                                    · rcases p616_3 (m.d 1 4) (by simp) with h640 | h640
                                      · linarith only [h484, h640, hlam]
                                      · linarith only [h486, h640, hlam]
                                  · linarith only [h483, h637, hlam]
                                · linarith only [h1, h636, hlam]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h645 | h645
                                · rcases p616_3 (m.d 1 2) (by simp) with h646 | h646
                                  · rcases p616_3 (m.d 1 3) (by simp) with h647 | h647
                                    · linarith only [h483, h647, hlam]
                                    · rcases p616_3 (m.d 1 4) (by simp) with h649 | h649
                                      · linarith only [h484, h649, hlam]
                                      · rcases p616_3 (m.d 1 5) (by simp) with h651 | h651
                                        · linarith only [h485, h651, hlam]
                                        · linarith only [h551, h651, hlam]
                                  · linarith only [h484, h646, hlam]
                                · linarith only [h2, h645, hlam]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p616_1, u2elo0, u5ehi1]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h1, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h483, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h486, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h549, hlam, p616_1]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h2, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h484, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h2, h293, hc13, hc45, hlam, hphi, ht34, p616_1]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h551, hlam, p616_1]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h3, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [h485, hlam, p616_0]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h669 | h669
                                · rcases p616_3 (m.d 1 2) (by simp) with h670 | h670
                                  · rcases p616_3 (m.d 1 3) (by simp) with h671 | h671
                                    · linarith only [h549, h671, hlam]
                                    · rcases p616_3 (m.d 1 4) (by simp) with h673 | h673
                                      · linarith only [h551, h673, hlam]
                                      · linarith only [h486, h673, hlam]
                                  · linarith only [h483, h670, hlam]
                                · linarith only [h1, h669, hlam]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                rcases p616_3 (m.d 0 1) (by simp) with h678 | h678
                                · rcases p616_3 (m.d 1 2) (by simp) with h679 | h679
                                  · rcases p616_3 (m.d 1 3) (by simp) with h680 | h680
                                    · linarith only [h549, h680, hlam]
                                    · rcases p616_3 (m.d 1 4) (by simp) with h682 | h682
                                      · linarith only [h551, h682, hlam]
                                      · rcases p616_3 (m.d 1 5) (by simp) with h684 | h684
                                        · rcases h1emin with h685 | h685 | h685 | h685 | h685
                                          · rcases h5bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h484, h553, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p616_1, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht5b, p686_1, u2elo0, u5ehi2]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h7, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h293, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h3, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p686_1, u5ehi2]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h549, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h551, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h6, hlam, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h485, hlam, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h555, hlam, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h557, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h3, h484, h553, hc23, hc35, hlam, hphi, p616_1, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h484, h553, hc23, hc35, hlam, hphi, p616_1, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              rcases p686_3 (m.d 0 5) (by simp) with h704 | h704
                                              · linarith only [h7, h704, hlam]
                                              · linarith only [h6, h704, hlam]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h559, hlam, p686_0]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h3, h484, h553, hc23, hc45, hlam, hphi, ht34, p616_1, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h484, h553, hc23, hc45, hlam, hphi, ht34, p616_1, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              rcases p686_3 (m.d 0 5) (by simp) with h711 | h711
                                              · linarith only [h293, h711, hlam]
                                              · linarith only [h6, h711, hlam]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [h1, h483, h7, hc23, hc45, hlam, hphi, ht34, p686_1]
                                            · have p686_0 := h686c.1
                                              have p686_1 := h686c.2.1
                                              have p686_2 := h686c.2.2.1
                                              have p686_3 := h686c.2.2.2
                                              linarith only [hlam, p686_0]
                                          · linarith only [h0, h685, hlam, ht12, u2elo0]
                                          · linarith only [h3, h484, h486, h553, h6, h685, hc23, hc34, hlam, hphi, ht12, p616_1, u2elo0]
                                          · linarith only [h3, h6, h685, hlam, ht12, p616_1, u2elo0]
                                          · linarith only [h3, h6, h685, hlam, ht12, u2elo0]
                                        · linarith only [h551, h684, hlam]
                                  · linarith only [h484, h679, hlam]
                                · linarith only [h2, h678, hlam]
                              · have p616_0 := h616c.1
                                have p616_1 := h616c.2.1
                                have p616_2 := h616c.2.2.1
                                have p616_3 := h616c.2.2.2
                                linarith only [hlam, p616_0]
              · linarith only [h485, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h483, h484, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h4, h483, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h727 | h727
      · linarith only [h4, h6, h727, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
        · linarith only [h5, h6, h729, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
          · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
            · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
              · linarith only [h6, h733, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
                  · linarith only [h1, h4, h6, h727, h736, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h738 | h738
                    · linarith only [h2, h729, h738, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                      · linarith only [h4, h6, h740, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h1, h4, h6, h735, h740, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
                  · linarith only [h2, h5, h6, h727, h735, h743, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h745 | h745
                    · linarith only [h2, h729, h745, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h747 | h747
                      · linarith only [h4, h6, h735, h747, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h749 | h749
                        · linarith only [h0, h6, h727, h732, h747, h749, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h751 | h751
                          · linarith only [h0, h6, h729, h732, h751, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h753 | h753
                            · linarith only [h0, h6, h732, h747, h751, h753, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 1) (by simp) with h757 | h757
                                · rcases p755_3 (m.d 1 2) (by simp) with h758 | h758
                                  · linarith only [h758, hlam, p755_0]
                                  · rcases p755_3 (m.d 1 3) (by simp) with h760 | h760
                                    · linarith only [h1, h760, hlam]
                                    · rcases p755_3 (m.d 1 4) (by simp) with h762 | h762
                                      · linarith only [h2, h762, hlam]
                                      · rcases p755_3 (m.d 1 5) (by simp) with h764 | h764
                                        · linarith only [h3, h764, hlam]
                                        · linarith only [h733, h764, hlam]
                                · linarith only [h757, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 1) (by simp) with h768 | h768
                                · rcases p755_3 (m.d 1 2) (by simp) with h769 | h769
                                  · linarith only [h0, h769, hlam]
                                  · linarith only [h731, h769, hlam]
                                · linarith only [h768, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 1) (by simp) with h773 | h773
                                · rcases p755_3 (m.d 1 2) (by simp) with h774 | h774
                                  · linarith only [h0, h774, hlam]
                                  · linarith only [h732, h774, hlam]
                                · linarith only [h773, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 1) (by simp) with h778 | h778
                                · rcases p755_3 (m.d 1 2) (by simp) with h779 | h779
                                  · linarith only [h0, h779, hlam]
                                  · rcases p755_3 (m.d 1 3) (by simp) with h781 | h781
                                    · linarith only [h1, h781, hlam]
                                    · rcases p755_3 (m.d 1 4) (by simp) with h783 | h783
                                      · linarith only [h2, h783, hlam]
                                      · rcases p755_3 (m.d 1 5) (by simp) with h785 | h785
                                        · linarith only [h785, hlam, p755_0]
                                        · rcases h1emin with h787 | h787 | h787 | h787 | h787
                                          · rcases h5bigk with h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h6, h732, h733, h747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p788_1, u2elo4]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h6, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h727, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h729, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h3, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h733, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h743, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h745, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo4, u5ehi0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h732, h733, h747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p788_1, u2elo4]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h749, hlam, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h751, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h3, h732, h733, h747, hc23, hc35, hlam, hphi, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h732, h733, h747, h753, hc23, hc45, hlam, hphi, ht34, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h0, h6, h732, h747, h753, hc23, hc45, hlam, hphi, ht34, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h753, hlam, p788_0]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h3, h732, h733, h747, hc23, hc45, hlam, hphi, ht34, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h732, h733, h747, hc23, hc45, hlam, hphi, ht34, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h0, h6, h732, h747, hc23, hc45, hlam, hphi, ht34, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [h1, h727, h731, hc23, hc45, hlam, hphi, ht34, p788_1]
                                            · have p788_0 := h788c.1
                                              have p788_1 := h788c.2.1
                                              have p788_2 := h788c.2.2.1
                                              have p788_3 := h788c.2.2.2
                                              linarith only [hlam, p788_0]
                                          · linarith only [h733, h787, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p755_1]
                                          · linarith only [h1, h4, h6, h787, hlam, ht12, u2elo4]
                                          · linarith only [h2, h5, h6, h787, hlam, ht12, u2elo4]
                                          · linarith only [h0, h6, h732, h747, h787, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p755_1, u2elo4]
                                · linarith only [h778, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h0, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h0, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u2elo4]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h0, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p755_1, u2elo4]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h733, hlam, p755_1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h1, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h731, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h735, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h743, hlam, p755_1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h2, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h732, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h2, h5, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u2elo4]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h745, hlam, p755_1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h3, hlam, p755_0]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [h3, h732, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p755_1]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 1) (by simp) with h836 | h836
                                · rcases p755_3 (m.d 1 2) (by simp) with h837 | h837
                                  · linarith only [h733, h837, hlam]
                                  · linarith only [h731, h837, hlam]
                                · linarith only [h1, h836, hlam]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                rcases p755_3 (m.d 0 1) (by simp) with h841 | h841
                                · rcases p755_3 (m.d 1 2) (by simp) with h842 | h842
                                  · linarith only [h733, h842, hlam]
                                  · linarith only [h732, h842, hlam]
                                · linarith only [h2, h841, hlam]
                              · have p755_0 := h755c.1
                                have p755_1 := h755c.2.1
                                have p755_2 := h755c.2.2.1
                                have p755_3 := h755c.2.2.2
                                linarith only [hlam, p755_0]
            · linarith only [h5, h6, h732, hc12, hlam, hphi, u2elo4]
          · linarith only [h4, h6, h731, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h849 | h849
    · linarith only [h5, h849, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h851 | h851
      · linarith only [h4, h5, h851, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h853 | h853
        · rcases m.htr 1 2 3 (by decide) (by decide) with h854 | h854
          · rcases m.htr 1 2 4 (by decide) (by decide) with h855 | h855
            · linarith only [h5, h855, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h857 | h857
              · linarith only [h0, h849, h857, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h859 | h859
                · linarith only [h854, h855, h859, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h861 | h861
                  · linarith only [h851, h859, h861, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h863 | h863
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h864 | h864
                      · linarith only [h859, h863, h864, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h866 | h866
                        · linarith only [h0, h849, h851, h854, h866, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h868 | h868
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h869 | h869
                            · rcases h1bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                rcases p870_3 (m.d 0 1) (by simp) with h872 | h872
                                · rcases p870_3 (m.d 1 2) (by simp) with h873 | h873
                                  · linarith only [h873, hlam, p870_0]
                                  · rcases p870_3 (m.d 1 3) (by simp) with h875 | h875
                                    · linarith only [h1, h875, hlam]
                                    · rcases p870_3 (m.d 1 4) (by simp) with h877 | h877
                                      · linarith only [h2, h877, hlam]
                                      · linarith only [h855, h877, hlam]
                                · linarith only [h872, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                rcases p870_3 (m.d 0 1) (by simp) with h881 | h881
                                · rcases p870_3 (m.d 1 2) (by simp) with h882 | h882
                                  · linarith only [h0, h882, hlam]
                                  · linarith only [h854, h882, hlam]
                                · linarith only [h881, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h863, hc01, hlam, hphi, ht0b, ht5b, p870_1, u5ehi4]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                rcases p870_3 (m.d 0 1) (by simp) with h887 | h887
                                · rcases p870_3 (m.d 1 2) (by simp) with h888 | h888
                                  · linarith only [h0, h888, hlam]
                                  · rcases p870_3 (m.d 1 3) (by simp) with h890 | h890
                                    · linarith only [h1, h890, hlam]
                                    · rcases p870_3 (m.d 1 4) (by simp) with h892 | h892
                                      · linarith only [h2, h892, hlam]
                                      · linarith only [h863, h892, hlam]
                                · linarith only [h887, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h0, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h0, h849, h868, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p870_1, u2elo3]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h855, hlam, p870_1]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h857, hlam, p870_1]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h1, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h854, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h859, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h861, hlam, p870_1]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h2, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h2, h5, hc12, hlam, hphi, p870_1, u2elo3]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                rcases p870_3 (m.d 0 1) (by simp) with h908 | h908
                                · rcases p870_3 (m.d 1 2) (by simp) with h909 | h909
                                  · linarith only [h855, h909, hlam]
                                  · linarith only [h854, h909, hlam]
                                · linarith only [h1, h908, hlam]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h2, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, p870_1, u2elo3, u5ehi1]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h3, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h3, h854, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p870_1]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                rcases p870_3 (m.d 0 1) (by simp) with h917 | h917
                                · rcases p870_3 (m.d 1 2) (by simp) with h918 | h918
                                  · linarith only [h857, h918, hlam]
                                  · linarith only [h854, h918, hlam]
                                · linarith only [h1, h917, hlam]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [h863, hlam, p870_0]
                              · have p870_0 := h870c.1
                                have p870_1 := h870c.2.1
                                have p870_2 := h870c.2.2.1
                                have p870_3 := h870c.2.2.2
                                linarith only [hlam, p870_0]
                            · linarith only [h0, h849, h854, h864, h868, h869, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h2, h5, h854, h863, h868, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h5, h853, h854, h855, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h4, h849, h854, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
          · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
            · linarith only [h5, h929, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
              · linarith only [h0, h5, h849, h931, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h933 | h933
                · linarith only [h928, h929, h933, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h935 | h935
                  · linarith only [h851, h933, h935, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
                    · linarith only [h2, h853, h937, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
                      · linarith only [h0, h5, h928, h939, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h941 | h941
                        · linarith only [h0, h5, h851, h853, h928, h941, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h943 | h943
                          · linarith only [h2, h853, h928, h929, h943, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · linarith only [h0, h5, h928, h943, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h928, hc12, hlam, hphi, u2elo3]

end R2N4
