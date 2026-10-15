import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
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
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h0, h10, h17, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h16, h17, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h16, h20, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                            · linarith only [h0, h11, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                              · linarith only [h0, h10, h13, h16, h22, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h16, h24, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h0, h10, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h14, h15, h27, h28, h9, hc34, hlam, hphi, ht45, u5elo0]
                        · linarith only [h13, h15, h27, h9, hc23, hlam, hphi, ht34, ht45, u5elo0]
                    · linarith only [h13, h14, h8, hc34, hlam, hphi, ht45, u5elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h13, h33, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                        · linarith only [h10, h33, h36, h8, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h10, h33, h38, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h0, h11, h40, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                              · rcases h2bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h11, h35, h36, h40, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h13, h35, h36, h4, h40, h7, hlam, p43_2]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h13, h35, h4, h40, h7, hlam, p43_2]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  rcases p43_3 (m.d 0 2) (by simp) with h48 | h48
                                  · rcases p43_3 (m.d 1 2) (by simp) with h49 | h49
                                    · linarith only [h0, h49, hlam]
                                    · linarith only [h12, h49, hlam]
                                  · linarith only [h48, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  rcases p43_3 (m.d 0 2) (by simp) with h55 | h55
                                  · rcases p43_3 (m.d 1 2) (by simp) with h56 | h56
                                    · rcases p43_3 (m.d 2 3) (by simp) with h57 | h57
                                      · linarith only [h57, hlam, p43_0]
                                      · rcases p43_3 (m.d 2 4) (by simp) with h59 | h59
                                        · linarith only [h11, h59, hlam]
                                        · linarith only [h36, h59, hlam]
                                    · linarith only [h56, hlam, p43_0]
                                  · linarith only [h4, h55, hlam]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  rcases p43_3 (m.d 0 2) (by simp) with h64 | h64
                                  · rcases p43_3 (m.d 1 2) (by simp) with h65 | h65
                                    · rcases p43_3 (m.d 2 3) (by simp) with h66 | h66
                                      · linarith only [h10, h66, hlam]
                                      · rcases p43_3 (m.d 2 4) (by simp) with h68 | h68
                                        · linarith only [h68, hlam, p43_0]
                                        · rcases p43_3 (m.d 2 5) (by simp) with h70 | h70
                                          · linarith only [h12, h70, hlam]
                                          · linarith only [h40, h70, hlam]
                                    · linarith only [h65, hlam, p43_0]
                                  · linarith only [h5, h64, hlam]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p43_1, u5ehi7]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h4, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h10, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h36, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h38, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h5, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h11, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h13, h35, h4, h40, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43_1]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h40, hlam, p43_1]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h6, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h12, hlam, p43_0]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p43_1, u5elo2]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [h0, h13, h35, h4, h40, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p43_1]
                                · have p43_0 := h43c.1
                                  have p43_1 := h43c.2.1
                                  have p43_2 := h43c.2.2.1
                                  have p43_3 := h43c.2.2.2
                                  linarith only [hlam, p43_0]
                              · linarith only [h13, h35, h42, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                        · linarith only [h10, h13, h35, h9, h92, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                          · linarith only [h10, h13, h33, h35, h9, h94, hlam, hphi, u5ehi6, u5elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h0, h11, h13, h35, h96, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                              · rcases h2bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p99_1, u5ehi7]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h10, h13, h35, h4, h7, h98, hlam, p99_2]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h11, h35, h4, h7, h98, hlam, p99_2]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  rcases p99_3 (m.d 0 2) (by simp) with h104 | h104
                                  · rcases p99_3 (m.d 1 2) (by simp) with h105 | h105
                                    · linarith only [h0, h105, hlam]
                                    · linarith only [h105, h12, hlam]
                                  · linarith only [h104, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h0, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  rcases p99_3 (m.d 0 2) (by simp) with h111 | h111
                                  · rcases p99_3 (m.d 1 2) (by simp) with h112 | h112
                                    · rcases p99_3 (m.d 2 3) (by simp) with h113 | h113
                                      · linarith only [h113, hlam, p99_0]
                                      · rcases p99_3 (m.d 2 4) (by simp) with h115 | h115
                                        · linarith only [h11, h115, hlam]
                                        · linarith only [h115, h92, hlam]
                                    · linarith only [h112, hlam, p99_0]
                                  · linarith only [h111, h4, hlam]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  rcases p99_3 (m.d 0 2) (by simp) with h120 | h120
                                  · rcases p99_3 (m.d 1 2) (by simp) with h121 | h121
                                    · rcases p99_3 (m.d 2 3) (by simp) with h122 | h122
                                      · linarith only [h10, h122, hlam]
                                      · rcases p99_3 (m.d 2 4) (by simp) with h124 | h124
                                        · linarith only [h124, hlam, p99_0]
                                        · rcases p99_3 (m.d 2 5) (by simp) with h126 | h126
                                          · linarith only [h12, h126, hlam]
                                          · linarith only [h126, h96, hlam]
                                    · linarith only [h121, hlam, p99_0]
                                  · linarith only [h120, h5, hlam]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p99_1, u5ehi7]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h4, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h10, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h92, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h94, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h5, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h11, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p99_1]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h96, hlam, p99_1]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h6, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h12, hlam, p99_0]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h12, hc23, hlam, hphi, ht34, ht45, p99_1, u5elo1]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [h12, h35, h4, h7, h98, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p99_1]
                                · have p99_0 := h99c.1
                                  have p99_1 := h99c.2.1
                                  have p99_2 := h99c.2.2.1
                                  have p99_3 := h99c.2.2.2
                                  linarith only [hlam, p99_0]
                              · linarith only [h13, h9, h98, hc13, hlam, hphi, ht34, ht45, u5elo0]
                · linarith only [h10, h12, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
                · linarith only [h0, h11, h149, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h10, h149, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
              · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
                · linarith only [h0, h10, h153, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h152, h153, h6, hc24, hlam, hphi, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                · linarith only [h0, h152, h156, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                              · linarith only [h1, h158, h164, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · rcases h2bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  rcases p166_3 (m.d 0 2) (by simp) with h168 | h168
                                  · rcases p166_3 (m.d 1 2) (by simp) with h169 | h169
                                    · linarith only [h0, h169, hlam]
                                    · rcases p166_3 (m.d 2 3) (by simp) with h171 | h171
                                      · linarith only [h171, h4, hlam]
                                      · linarith only [h10, h171, hlam]
                                  · linarith only [h0, h168, hlam]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h0, h152, h160, h161, h164, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h0, h152, h160, h164, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  rcases p166_3 (m.d 0 2) (by simp) with h177 | h177
                                  · rcases p166_3 (m.d 1 2) (by simp) with h178 | h178
                                    · linarith only [h0, h178, hlam]
                                    · rcases p166_3 (m.d 2 3) (by simp) with h180 | h180
                                      · linarith only [h180, h4, hlam]
                                      · linarith only [h162, h180, hlam]
                                  · linarith only [h177, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h0, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h10, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h152, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h156, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h4, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  rcases p166_3 (m.d 0 2) (by simp) with h190 | h190
                                  · rcases p166_3 (m.d 1 2) (by simp) with h191 | h191
                                    · linarith only [h191, hlam, p166_0]
                                    · rcases p166_3 (m.d 2 3) (by simp) with h193 | h193
                                      · rcases p166_3 (m.d 2 4) (by simp) with h194 | h194
                                        · linarith only [h161, h194, hlam]
                                        · linarith only [h152, h194, hlam]
                                      · linarith only [h193, hlam, p166_0]
                                  · linarith only [h0, h190, hlam]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h152, h160, h164, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h0, h156, h4, hc01, hlam, hphi, ht0b, ht5b, p166_1, u5ehi6]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h5, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  rcases p166_3 (m.d 0 2) (by simp) with h203 | h203
                                  · rcases p166_3 (m.d 1 2) (by simp) with h204 | h204
                                    · linarith only [h204, hlam, p166_0]
                                    · rcases p166_3 (m.d 2 3) (by simp) with h206 | h206
                                      · rcases p166_3 (m.d 2 4) (by simp) with h207 | h207
                                        · rcases p166_3 (m.d 2 5) (by simp) with h208 | h208
                                          · linarith only [h163, h208, hlam]
                                          · linarith only [h156, h208, hlam]
                                        · linarith only [h207, hlam, p166_0]
                                      · linarith only [h10, h206, hlam]
                                  · linarith only [h0, h203, hlam]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h161, hlam, p166_1]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h0, h156, h161, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p166_1]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h6, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p166_1, u5elo2]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h162, hlam, p166_1]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [h163, hlam, p166_0]
                                · have p166_0 := h166c.1
                                  have p166_1 := h166c.2.1
                                  have p166_2 := h166c.2.2.1
                                  have p166_3 := h166c.2.2.2
                                  linarith only [hlam, p166_0]
                            · linarith only [h152, h160, h163, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
                          · linarith only [h10, h158, h160, h162, hlam, hphi, u5ehi9, u5elo3]
                        · linarith only [h0, h10, h158, h160, h161, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h228 | h228
                              · linarith only [h158, h160, h228, hlam]
                              · rcases h2bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h152, h160, h225, h227, h4, hlam, p230_2]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h0, h160, h225, h227, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p230_1]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h0, h158, h160, h227, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p230_1]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  rcases p230_3 (m.d 0 2) (by simp) with h235 | h235
                                  · rcases p230_3 (m.d 1 2) (by simp) with h236 | h236
                                    · linarith only [h0, h236, hlam]
                                    · rcases p230_3 (m.d 2 3) (by simp) with h238 | h238
                                      · linarith only [h238, h4, hlam]
                                      · linarith only [h226, h238, hlam]
                                  · linarith only [h235, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h0, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h10, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h152, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h156, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h4, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  rcases p230_3 (m.d 0 2) (by simp) with h248 | h248
                                  · rcases p230_3 (m.d 1 2) (by simp) with h249 | h249
                                    · linarith only [h249, hlam, p230_0]
                                    · rcases p230_3 (m.d 2 3) (by simp) with h251 | h251
                                      · rcases p230_3 (m.d 2 4) (by simp) with h252 | h252
                                        · linarith only [h225, h252, hlam]
                                        · linarith only [h152, h252, hlam]
                                      · linarith only [h251, hlam, p230_0]
                                  · linarith only [h0, h248, hlam]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h152, h160, h227, hc12, hc23, hlam, hphi, p230_1]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p230_1, u5ehi7]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h5, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  rcases p230_3 (m.d 0 2) (by simp) with h261 | h261
                                  · rcases p230_3 (m.d 1 2) (by simp) with h262 | h262
                                    · linarith only [h262, hlam, p230_0]
                                    · rcases p230_3 (m.d 2 3) (by simp) with h264 | h264
                                      · rcases p230_3 (m.d 2 4) (by simp) with h265 | h265
                                        · rcases p230_3 (m.d 2 5) (by simp) with h266 | h266
                                          · linarith only [h227, h266, hlam]
                                          · linarith only [h156, h266, hlam]
                                        · linarith only [h265, hlam, p230_0]
                                      · linarith only [h10, h264, hlam]
                                  · linarith only [h0, h261, hlam]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h225, hlam, p230_1]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h152, h160, h227, hc12, hc24, hlam, hphi, p230_1]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h6, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p230_1, u5elo2]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h226, hlam, p230_1]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [h227, hlam, p230_0]
                                · have p230_0 := h230c.1
                                  have p230_1 := h230c.2.1
                                  have p230_2 := h230c.2.2.1
                                  have p230_3 := h230c.2.2.2
                                  linarith only [hlam, p230_0]
                            · linarith only [h152, h227, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h10, h226, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h10, h159, h225, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · linarith only [h158, h159, h8, hc34, hlam, hphi, ht45, u5elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                    · linarith only [h0, h158, h284, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h286 | h286
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h287 | h287
                        · linarith only [h0, h158, h286, h287, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h289 | h289
                          · linarith only [h0, h287, h289, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h10, h289, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                              · linarith only [h0, h286, h292, h295, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h10, h158, h295, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h152, h294, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                          · linarith only [h10, h293, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h300 | h300
                          · linarith only [h0, h292, h300, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h10, h300, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
            · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
              · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                      · linarith only [h2, h308, h9, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h311 | h311
                          · linarith only [h0, h303, h311, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h310, h311, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h310, h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h306, h307, h8, h9, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h306, h7, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h303, h305, h6, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h303, h304, h5, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
              · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                · linarith only [h0, h303, h320, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h319, h320, h6, h9, hc24, hlam, hphi, ht45, u5elo4]
              · linarith only [h319, h5, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h325 | h325
        · rcases m.htr 0 4 5 (by decide) (by decide) with h326 | h326
          · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
            · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
              · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
                · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                  · linarith only [h325, h330, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h332 | h332
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                        · linarith only [h0, h1, h327, h332, h334, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h336 | h336
                          · linarith only [h0, h328, h334, h336, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · linarith only [h1, h332, h336, h7, hc23, hc34, hlam, hphi]
                      · linarith only [h330, h332, h333, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h325, h332, h7, hc13, hc34, hlam, hphi]
                · linarith only [h327, h329, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                · linarith only [h0, h328, h342, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h327, h342, h6, hc23, hlam, hphi, ht34, ht45, u5elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
              · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                · linarith only [h327, h346, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h345, h346, h6, hc24, hlam, hphi, ht45, u5elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                · linarith only [h0, h345, h349, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                  · linarith only [h325, h351, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                        · linarith only [h355, h4, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                              · rcases h2bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  rcases p360_3 (m.d 0 2) (by simp) with h362 | h362
                                  · rcases p360_3 (m.d 1 2) (by simp) with h363 | h363
                                    · linarith only [h0, h363, hlam]
                                    · rcases p360_3 (m.d 2 3) (by simp) with h365 | h365
                                      · linarith only [h365, h4, hlam]
                                      · linarith only [h327, h365, hlam]
                                  · linarith only [h0, h362, hlam]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h0, h327, h353, h359, hc01, hlam, hphi, ht0b, ht5b, p360_1, u5ehi9]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h0, h345, h351, h353, h359, hc01, hlam, hphi, ht0b, ht5b, p360_1, u5ehi9]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  rcases p360_3 (m.d 0 2) (by simp) with h371 | h371
                                  · rcases p360_3 (m.d 1 2) (by simp) with h372 | h372
                                    · linarith only [h0, h372, hlam]
                                    · rcases p360_3 (m.d 2 3) (by simp) with h374 | h374
                                      · linarith only [h374, h4, hlam]
                                      · linarith only [h357, h374, hlam]
                                  · linarith only [h371, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h0, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h327, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h345, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h349, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h4, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p360_1]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h355, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h349, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p360_1, u5ehi6]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h5, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  rcases p360_3 (m.d 0 2) (by simp) with h389 | h389
                                  · rcases p360_3 (m.d 1 2) (by simp) with h390 | h390
                                    · linarith only [h390, hlam, p360_0]
                                    · rcases p360_3 (m.d 2 3) (by simp) with h392 | h392
                                      · linarith only [h355, h392, hlam]
                                      · linarith only [h327, h392, hlam]
                                  · linarith only [h0, h389, hlam]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h327, h353, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p360_1, u5ehi8]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h0, h327, h349, h353, h359, h4, h5, h7, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht5b, p360_1, u5ehi9]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h6, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h327, h353, h359, h4, h7, hc12, hc34, hlam, hphi, ht23, p360_1, u5ehi9, u5elo2]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h357, hlam, p360_1]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [h358, hlam, p360_0]
                                · have p360_0 := h360c.1
                                  have p360_1 := h360c.2.1
                                  have p360_2 := h360c.2.2.1
                                  have p360_3 := h360c.2.2.2
                                  linarith only [hlam, p360_0]
                              · linarith only [h327, h353, h359, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                            · linarith only [h326, h345, h358, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                          · linarith only [h327, h353, h357, hlam]
                      · linarith only [h351, h353, h354, hlam, hphi, u5ehi8, u5elo4]
                    · linarith only [h325, h353, h7, hc13, hc34, hlam, hphi]
          · linarith only [h325, h326, h7, hlam, hphi, u5ehi8, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h410 | h410
          · rcases m.htr 1 2 3 (by decide) (by decide) with h411 | h411
            · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
              · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
                · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                  · linarith only [h1, h410, h414, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h416 | h416
                    · linarith only [h1, h325, h416, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                        · linarith only [h325, h4, h419, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h421 | h421
                          · linarith only [h325, h4, h421, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h423 | h423
                            · linarith only [h0, h412, h423, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h425 | h425
                              · rcases h2bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h0, h412, h418, h419, h423, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  rcases p426_3 (m.d 0 2) (by simp) with h429 | h429
                                  · rcases p426_3 (m.d 1 2) (by simp) with h430 | h430
                                    · linarith only [h0, h430, hlam]
                                    · linarith only [h411, h430, hlam]
                                  · linarith only [h429, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  rcases p426_3 (m.d 0 2) (by simp) with h434 | h434
                                  · rcases p426_3 (m.d 1 2) (by simp) with h435 | h435
                                    · linarith only [h0, h435, hlam]
                                    · linarith only [h412, h435, hlam]
                                  · linarith only [h434, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  rcases p426_3 (m.d 0 2) (by simp) with h439 | h439
                                  · rcases p426_3 (m.d 1 2) (by simp) with h440 | h440
                                    · linarith only [h0, h440, hlam]
                                    · linarith only [h413, h440, hlam]
                                  · linarith only [h439, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h0, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  rcases p426_3 (m.d 0 2) (by simp) with h446 | h446
                                  · rcases p426_3 (m.d 1 2) (by simp) with h447 | h447
                                    · rcases p426_3 (m.d 2 3) (by simp) with h448 | h448
                                      · linarith only [h448, hlam, p426_0]
                                      · rcases p426_3 (m.d 2 4) (by simp) with h450 | h450
                                        · linarith only [h412, h450, hlam]
                                        · linarith only [h419, h450, hlam]
                                    · linarith only [h447, hlam, p426_0]
                                  · linarith only [h4, h446, hlam]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  rcases p426_3 (m.d 0 2) (by simp) with h455 | h455
                                  · rcases p426_3 (m.d 1 2) (by simp) with h456 | h456
                                    · rcases p426_3 (m.d 2 3) (by simp) with h457 | h457
                                      · linarith only [h411, h457, hlam]
                                      · rcases p426_3 (m.d 2 4) (by simp) with h459 | h459
                                        · linarith only [h459, hlam, p426_0]
                                        · rcases p426_3 (m.d 2 5) (by simp) with h461 | h461
                                          · linarith only [h413, h461, hlam]
                                          · linarith only [h423, h461, hlam]
                                    · linarith only [h456, hlam, p426_0]
                                  · linarith only [h455, h5, hlam]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p426_1, u5ehi7]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h4, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h411, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h419, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h421, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h5, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h412, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h2, h418, h423, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h423, hlam, p426_1]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h6, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h413, hlam, p426_0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p426_1, u5elo2]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [h3, h418, h419, h423, hc23, hlam, hphi, ht34, ht45, p426_1, u5elo0]
                                · have p426_0 := h426c.1
                                  have p426_1 := h426c.2.1
                                  have p426_2 := h426c.2.2.1
                                  have p426_3 := h426c.2.2.2
                                  linarith only [hlam, p426_0]
                              · linarith only [h2, h418, h425, h7, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                        · linarith only [h410, h411, h414, h418, h483, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                          · linarith only [h325, h410, h411, h414, h418, h485, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                            · linarith only [h412, h418, h487, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                              · rcases h2bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h413, hc02, hlam, hphi, ht0b, ht5b, p490_1, u5ehi7]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  rcases p490_3 (m.d 0 2) (by simp) with h493 | h493
                                  · rcases p490_3 (m.d 1 2) (by simp) with h494 | h494
                                    · linarith only [h0, h494, hlam]
                                    · linarith only [h411, h494, hlam]
                                  · linarith only [h493, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  rcases p490_3 (m.d 0 2) (by simp) with h498 | h498
                                  · rcases p490_3 (m.d 1 2) (by simp) with h499 | h499
                                    · linarith only [h0, h499, hlam]
                                    · linarith only [h412, h499, hlam]
                                  · linarith only [h498, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  rcases p490_3 (m.d 0 2) (by simp) with h503 | h503
                                  · rcases p490_3 (m.d 1 2) (by simp) with h504 | h504
                                    · linarith only [h0, h504, hlam]
                                    · linarith only [h413, h504, hlam]
                                  · linarith only [h503, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h0, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  rcases p490_3 (m.d 0 2) (by simp) with h510 | h510
                                  · rcases p490_3 (m.d 1 2) (by simp) with h511 | h511
                                    · rcases p490_3 (m.d 2 3) (by simp) with h512 | h512
                                      · linarith only [h512, hlam, p490_0]
                                      · rcases p490_3 (m.d 2 4) (by simp) with h514 | h514
                                        · linarith only [h412, h514, hlam]
                                        · linarith only [h483, h514, hlam]
                                    · linarith only [h511, hlam, p490_0]
                                  · linarith only [h4, h510, hlam]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  rcases p490_3 (m.d 0 2) (by simp) with h519 | h519
                                  · rcases p490_3 (m.d 1 2) (by simp) with h520 | h520
                                    · rcases p490_3 (m.d 2 3) (by simp) with h521 | h521
                                      · linarith only [h411, h521, hlam]
                                      · rcases p490_3 (m.d 2 4) (by simp) with h523 | h523
                                        · linarith only [h523, hlam, p490_0]
                                        · rcases p490_3 (m.d 2 5) (by simp) with h525 | h525
                                          · linarith only [h413, h525, hlam]
                                          · linarith only [h487, h525, hlam]
                                    · linarith only [h520, hlam, p490_0]
                                  · linarith only [h5, h519, hlam]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p490_1, u5ehi7]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h4, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h411, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h483, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h485, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h5, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h412, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h325, h410, h412, h418, hc23, hlam, hphi, ht34, ht45, p490_1, u5elo3]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h487, hlam, p490_1]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h6, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h413, hlam, p490_0]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p490_1, u5elo2]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [h325, h410, h413, h418, hc24, hlam, hphi, ht45, p490_1, u5elo3]
                                · have p490_0 := h490c.1
                                  have p490_1 := h490c.2.1
                                  have p490_2 := h490c.2.2.1
                                  have p490_3 := h490c.2.2.2
                                  linarith only [hlam, p490_0]
                              · linarith only [h410, h489, h7, hlam]
                · linarith only [h325, h411, h413, h6, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                · linarith only [h412, h5, h548, hc02, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h325, h411, h548, h6, hc23, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h325, h4, h411, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h552 | h552
            · rcases m.htr 1 2 4 (by decide) (by decide) with h553 | h553
              · rcases m.htr 1 2 5 (by decide) (by decide) with h554 | h554
                · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                  · linarith only [h1, h555, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
                    · linarith only [h1, h325, h410, h557, h7, hlam, hphi, u5ehi5, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
                      · linarith only [h2, h410, h559, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                        · linarith only [h1, h552, h561, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h563 | h563
                          · linarith only [h1, h325, h552, h563, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
                            · linarith only [h2, h410, h553, h565, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h567 | h567
                              · rcases h2bigk with h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, h554, hc01, hlam, hphi, ht0b, ht5b, p568_1, u5ehi7]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h571 | h571
                                  · rcases p568_3 (m.d 1 2) (by simp) with h572 | h572
                                    · linarith only [h0, h572, hlam]
                                    · linarith only [h552, h572, hlam]
                                  · linarith only [h571, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h576 | h576
                                  · rcases p568_3 (m.d 1 2) (by simp) with h577 | h577
                                    · linarith only [h0, h577, hlam]
                                    · linarith only [h553, h577, hlam]
                                  · linarith only [h576, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h581 | h581
                                  · rcases p568_3 (m.d 1 2) (by simp) with h582 | h582
                                    · linarith only [h0, h582, hlam]
                                    · linarith only [h554, h582, hlam]
                                  · linarith only [h581, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h588 | h588
                                  · rcases p568_3 (m.d 1 2) (by simp) with h589 | h589
                                    · rcases p568_3 (m.d 2 3) (by simp) with h590 | h590
                                      · linarith only [h590, hlam, p568_0]
                                      · rcases p568_3 (m.d 2 4) (by simp) with h592 | h592
                                        · linarith only [h553, h592, hlam]
                                        · linarith only [h561, h592, hlam]
                                    · linarith only [h589, hlam, p568_0]
                                  · linarith only [h4, h588, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 2) (by simp) with h597 | h597
                                  · rcases p568_3 (m.d 1 2) (by simp) with h598 | h598
                                    · rcases p568_3 (m.d 2 3) (by simp) with h599 | h599
                                      · linarith only [h552, h599, hlam]
                                      · rcases p568_3 (m.d 2 4) (by simp) with h601 | h601
                                        · linarith only [h601, hlam, p568_0]
                                        · rcases p568_3 (m.d 2 5) (by simp) with h603 | h603
                                          · linarith only [h554, h603, hlam]
                                          · linarith only [h565, h603, hlam]
                                    · linarith only [h598, hlam, p568_0]
                                  · linarith only [h5, h597, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p568_1, u5ehi7]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h4, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h552, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h561, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h563, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h5, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h553, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h2, h410, h553, h567, hc23, hlam, hphi, ht34, ht45, p568_1, u5elo3]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h565, hlam, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h6, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h554, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h3, h554, hc23, hlam, hphi, ht34, ht45, p568_1, u5elo0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h3, h410, h554, h567, hc24, hlam, hphi, ht45, p568_1, u5elo3]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                              · linarith only [h567, h7, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h325, h552, h554, h6, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h410, h5, h552, h553, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h4, h410, h552, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
    · linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h629 | h629
    · rcases m.htr 0 3 4 (by decide) (by decide) with h630 | h630
      · linarith only [h4, h5, h630, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h632 | h632
        · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
          · rcases m.htr 1 2 3 (by decide) (by decide) with h634 | h634
            · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
              · linarith only [h4, h5, h632, h635, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                  · linarith only [h0, h630, h632, h634, h638, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h640 | h640
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h642 | h642
                        · linarith only [h2, h4, h5, h630, h635, h642, hc12, hc24, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                          · linarith only [h4, h5, h642, h644, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                          · linarith only [h0, h5, h634, h640, h642, h644, hc23, hc34, hlam, hphi]
                      · linarith only [h633, h634, h635, h641, hc23, hlam, hphi, ht34, ht45, u5elo0]
                    · linarith only [h630, h632, h640, hc13, hc34, hlam, hphi]
                · linarith only [h5, h629, h637, hc12, hc24, hlam, hphi]
            · linarith only [h4, h5, h634, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h633, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
          · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
            · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
              · linarith only [h5, h629, h654, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h656 | h656
                · rcases m.htr 1 3 4 (by decide) (by decide) with h657 | h657
                  · linarith only [h1, h632, h657, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h659 | h659
                    · linarith only [h1, h632, h659, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                        · linarith only [h4, h5, h630, h662, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
                          · linarith only [h1, h632, h653, h664, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                              · rcases h2bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h5, h656, h662, h666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p668_1, u5ehi9]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h5, h662, hc23, hc34, hlam, hphi, p668_1]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h5, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h5, h662, h666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p668_1, u5ehi9]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h0, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h0, h5, h662, hc23, hc34, hlam, hphi, p668_1]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h654, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h0, h5, h662, h666, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p668_1, u5ehi9]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h4, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h653, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h662, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h664, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h4, h662, hc23, hc34, hlam, hphi, p668_1]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h653, h662, hc23, hc34, hlam, hphi, p668_1]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  rcases p668_3 (m.d 0 2) (by simp) with h686 | h686
                                  · linarith only [h5, h686, hlam]
                                  · linarith only [h4, h686, hlam]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  rcases p668_3 (m.d 0 2) (by simp) with h690 | h690
                                  · linarith only [h5, h690, hlam]
                                  · linarith only [h629, h690, hlam]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h629, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h656, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p668_1, u5elo2]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [h666, hlam, p668_0]
                                · have p668_0 := h668c.1
                                  have p668_1 := h668c.2.1
                                  have p668_2 := h668c.2.2.1
                                  have p668_3 := h668c.2.2.2
                                  linarith only [hlam, p668_0]
                              · linarith only [h0, h5, h656, h662, h667, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                            · linarith only [h0, h2, h5, h656, h661, h666, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
                      · linarith only [h632, h652, h654, h656, h661, hlam, hphi, u5ehi7, u5elo3]
                · linarith only [h5, h629, h656, hc12, hc24, hlam, hphi]
            · linarith only [h4, h5, h653, hc12, hc24, hlam, hphi]
          · linarith only [h5, h629, h652, hlam, hphi, u5ehi7, u5elo4]
    · linarith only [h4, h629, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
