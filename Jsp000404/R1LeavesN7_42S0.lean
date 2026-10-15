import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h14, h15, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h1, h14, h18, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h20, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h0, h11, h14, h20, h22, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h14, h22, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h26, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h12, h13, h25, h26, h7, hc34, hlam, hphi, ht45, u5elo0]
                    · linarith only [h11, h13, h25, h7, hc23, hlam, hphi, ht34, ht45, u5elo0]
                · linarith only [h11, h12, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                · linarith only [h1, h11, h31, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                    · linarith only [h31, h34, h8, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                      · linarith only [h0, h31, h36, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                        · linarith only [h0, h38, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                          · rcases h1bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h33, h34, h38, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              rcases p41_3 (m.d 0 1) (by simp) with h44 | h44
                              · rcases p41_3 (m.d 1 2) (by simp) with h45 | h45
                                · linarith only [h0, h45, hlam]
                                · linarith only [h45, h8, hlam]
                              · linarith only [h44, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h33, h34, h38, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              rcases p41_3 (m.d 0 1) (by simp) with h50 | h50
                              · rcases p41_3 (m.d 1 2) (by simp) with h51 | h51
                                · linarith only [h0, h51, hlam]
                                · linarith only [h10, h51, hlam]
                              · linarith only [h50, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h0, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              rcases p41_3 (m.d 0 1) (by simp) with h57 | h57
                              · rcases p41_3 (m.d 1 2) (by simp) with h58 | h58
                                · rcases p41_3 (m.d 1 3) (by simp) with h59 | h59
                                  · linarith only [h59, h8, hlam]
                                  · rcases p41_3 (m.d 1 4) (by simp) with h61 | h61
                                    · linarith only [h61, h9, hlam]
                                    · linarith only [h11, h61, hlam]
                                · linarith only [h58, h8, hlam]
                              · linarith only [h1, h57, hlam]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h0, h33, h34, h38, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p41_1, u5ehi6]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h1, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h8, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h11, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h31, hlam, p41_1]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h2, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h9, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              rcases p41_3 (m.d 0 1) (by simp) with h75 | h75
                              · rcases p41_3 (m.d 1 2) (by simp) with h76 | h76
                                · rcases p41_3 (m.d 1 3) (by simp) with h77 | h77
                                  · linarith only [h11, h77, hlam]
                                  · rcases p41_3 (m.d 1 4) (by simp) with h79 | h79
                                    · rcases p41_3 (m.d 1 5) (by simp) with h80 | h80
                                      · linarith only [h33, h80, hlam]
                                      · linarith only [h31, h80, hlam]
                                    · linarith only [h11, h79, hlam]
                                · linarith only [h76, h8, hlam]
                              · linarith only [h1, h75, hlam]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h11, h33, h34, h38, hc23, hc34, hlam, hphi, p41_1]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h3, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h10, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [hc13, hlam, hphi, ht34, ht45, p41_1, u5elo1]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [h33, hlam, p41_0]
                            · have p41_0 := h41c.1
                              have p41_1 := h41c.2.1
                              have p41_2 := h41c.2.2.1
                              have p41_3 := h41c.2.2.2
                              linarith only [hlam, p41_0]
                          · linarith only [h11, h40, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h11, h8, h94, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h1, h11, h31, h6, h8, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi6]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h11, h33, h9, h98, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h100 | h100
                          · rcases h1bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h10, hc01, hlam, hphi, ht0b, ht5b, p101_1, u5ehi7]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h1, h100, h11, h33, h6, hlam, p101_2]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h1, h100, h33, h6, hlam, p101_2]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              rcases p101_3 (m.d 0 1) (by simp) with h106 | h106
                              · rcases p101_3 (m.d 1 2) (by simp) with h107 | h107
                                · linarith only [h0, h107, hlam]
                                · linarith only [h10, h107, hlam]
                              · linarith only [h106, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h0, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              rcases p101_3 (m.d 0 1) (by simp) with h113 | h113
                              · rcases p101_3 (m.d 1 2) (by simp) with h114 | h114
                                · rcases p101_3 (m.d 1 3) (by simp) with h115 | h115
                                  · linarith only [h115, h8, hlam]
                                  · rcases p101_3 (m.d 1 4) (by simp) with h117 | h117
                                    · linarith only [h117, h9, hlam]
                                    · linarith only [h11, h117, hlam]
                                · linarith only [h114, h8, hlam]
                              · linarith only [h1, h113, hlam]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              rcases p101_3 (m.d 0 1) (by simp) with h122 | h122
                              · rcases p101_3 (m.d 1 2) (by simp) with h123 | h123
                                · rcases p101_3 (m.d 1 3) (by simp) with h124 | h124
                                  · linarith only [h124, h8, hlam]
                                  · rcases p101_3 (m.d 1 4) (by simp) with h126 | h126
                                    · linarith only [h126, h9, hlam]
                                    · rcases p101_3 (m.d 1 5) (by simp) with h128 | h128
                                      · linarith only [h10, h128, hlam]
                                      · linarith only [h128, h33, hlam]
                                · linarith only [h123, h9, hlam]
                              · linarith only [h122, h2, hlam]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht5b, p101_1, u5ehi7]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h1, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h8, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h11, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h31, hlam, p101_1]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h2, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h9, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h1, h100, h33, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h33, hlam, p101_1]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h3, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h10, hlam, p101_0]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h8, hc23, hlam, hphi, ht34, ht45, p101_1, u5elo1]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [h1, h100, h33, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p101_1]
                            · have p101_0 := h101c.1
                              have p101_1 := h101c.2.1
                              have p101_2 := h101c.2.2.1
                              have p101_3 := h101c.2.2.2
                              linarith only [hlam, p101_0]
                          · linarith only [h100, h11, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h10, h5, h8, hc23, hlam, hphi, ht34, ht45, u5elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
            · linarith only [h0, h151, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · linarith only [h151, h5, h8, hc23, hlam, hphi, ht34, ht45, u5elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
          · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
            · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
              · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                        · linarith only [h154, h161, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h163 | h163
                          · linarith only [h159, h161, h163, hlam]
                          · rcases h1bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h154, h158, h159, h161, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h154, h158, h159, h161, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h158, h159, h161, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              rcases p165_3 (m.d 0 1) (by simp) with h170 | h170
                              · rcases p165_3 (m.d 1 2) (by simp) with h171 | h171
                                · linarith only [h0, h171, hlam]
                                · linarith only [h155, h171, hlam]
                              · linarith only [h170, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h0, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h8, hlam, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h158, h159, h161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p165_1, u5ehi6]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h1, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h1, h154, h159, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h1, h158, h159, h161, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h1, h155, h160, hc01, hlam, hphi, ht0b, ht5b, p165_1, u5ehi8]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h2, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h154, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h156, hlam, p165_1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h0, h154, h155, h160, hc01, hlam, hphi, ht0b, ht5b, p165_1, u5ehi8]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h3, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h155, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h157, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h158, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                      · linarith only [h160, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h154, h158, h159, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h154, h158, h199, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                          · linarith only [h154, h158, h197, h201, hlam]
                          · rcases h1bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h155, h198, hc01, hlam, hphi, ht0b, ht5b, p203_1, u5ehi8]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h155, h198, h8, hc01, hlam, hphi, ht0b, ht5b, p203_1, u5ehi8]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              rcases p203_3 (m.d 0 1) (by simp) with h207 | h207
                              · rcases p203_3 (m.d 1 2) (by simp) with h208 | h208
                                · linarith only [h0, h208, hlam]
                                · linarith only [h154, h208, hlam]
                              · linarith only [h207, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              rcases p203_3 (m.d 0 1) (by simp) with h212 | h212
                              · rcases p203_3 (m.d 1 2) (by simp) with h213 | h213
                                · linarith only [h0, h213, hlam]
                                · linarith only [h155, h213, hlam]
                              · linarith only [h212, hlam, p203_0]
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
                              linarith only [h8, hlam, p203_1]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              rcases p203_3 (m.d 0 1) (by simp) with h220 | h220
                              · rcases p203_3 (m.d 1 2) (by simp) with h221 | h221
                                · rcases p203_3 (m.d 1 3) (by simp) with h222 | h222
                                  · rcases p203_3 (m.d 1 4) (by simp) with h223 | h223
                                    · linarith only [h154, h223, hlam]
                                    · rcases p203_3 (m.d 1 5) (by simp) with h225 | h225
                                      · linarith only [h155, h225, hlam]
                                      · linarith only [h158, h225, hlam]
                                  · linarith only [h156, h222, hlam]
                                · linarith only [h154, h221, hlam]
                              · linarith only [h2, h220, hlam]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h155, h198, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p203_1, u5ehi8]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h1, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h1, h154, h197, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p203_1]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              rcases p203_3 (m.d 0 1) (by simp) with h235 | h235
                              · rcases p203_3 (m.d 1 2) (by simp) with h236 | h236
                                · linarith only [h236, h8, hlam]
                                · linarith only [h154, h236, hlam]
                              · linarith only [h2, h235, hlam]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h1, h155, h198, hc01, hlam, hphi, ht0b, ht5b, p203_1, u5ehi8]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h2, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h154, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h156, hlam, p203_1]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h158, hlam, p203_1]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h3, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h155, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h157, hlam, p203_0]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [h154, h197, hc34, hlam, hphi, ht45, p203_1, u5elo1]
                            · have p203_0 := h203c.1
                              have p203_1 := h203c.2.1
                              have p203_2 := h203c.2.2.1
                              have p203_3 := h203c.2.2.2
                              linarith only [hlam, p203_0]
                      · linarith only [h155, h198, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h155, h197, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h155, h157, h8, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h1, h155, h156, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · linarith only [h154, h155, h5, hc24, hlam, hphi, ht45, u5elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
            · linarith only [h0, h154, h256, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
              · rcases m.htr 1 3 5 (by decide) (by decide) with h259 | h259
                · rcases m.htr 1 4 5 (by decide) (by decide) with h260 | h260
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h262 | h262
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h263 | h263
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                          · linarith only [h1, h258, h264, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                          · rcases h1bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              rcases p266_3 (m.d 0 1) (by simp) with h268 | h268
                              · rcases p266_3 (m.d 1 2) (by simp) with h269 | h269
                                · linarith only [h269, hlam, p266_0]
                                · rcases p266_3 (m.d 1 3) (by simp) with h271 | h271
                                  · linarith only [h1, h271, hlam]
                                  · linarith only [h271, h8, hlam]
                              · linarith only [h268, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h258, h260, h264, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h260, h264, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              rcases p266_3 (m.d 0 1) (by simp) with h277 | h277
                              · rcases p266_3 (m.d 1 2) (by simp) with h278 | h278
                                · linarith only [h0, h278, hlam]
                                · rcases p266_3 (m.d 1 3) (by simp) with h280 | h280
                                  · linarith only [h1, h280, hlam]
                                  · linarith only [h259, h280, hlam]
                              · linarith only [h277, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h0, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h8, hlam, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h154, hlam, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h256, hlam, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h1, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              rcases p266_3 (m.d 0 1) (by simp) with h290 | h290
                              · rcases p266_3 (m.d 1 2) (by simp) with h291 | h291
                                · linarith only [h291, h8, hlam]
                                · rcases p266_3 (m.d 1 3) (by simp) with h293 | h293
                                  · rcases p266_3 (m.d 1 4) (by simp) with h294 | h294
                                    · linarith only [h258, h294, hlam]
                                    · linarith only [h154, h294, hlam]
                                  · linarith only [h293, h8, hlam]
                              · linarith only [h0, h290, hlam]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h260, h264, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p266_1, u5ehi6]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h2, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              rcases p266_3 (m.d 0 1) (by simp) with h303 | h303
                              · rcases p266_3 (m.d 1 2) (by simp) with h304 | h304
                                · linarith only [h154, h304, hlam]
                                · rcases p266_3 (m.d 1 3) (by simp) with h306 | h306
                                  · rcases p266_3 (m.d 1 4) (by simp) with h307 | h307
                                    · rcases p266_3 (m.d 1 5) (by simp) with h308 | h308
                                      · linarith only [h260, h308, hlam]
                                      · linarith only [h256, h308, hlam]
                                    · linarith only [h154, h307, hlam]
                                  · linarith only [h306, h8, hlam]
                              · linarith only [h0, h303, hlam]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h258, hlam, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h154, h260, h264, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p266_1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h3, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p266_1, u5elo1]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h259, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [h260, hlam, p266_0]
                            · have p266_0 := h266c.1
                              have p266_1 := h266c.2.1
                              have p266_2 := h266c.2.2.1
                              have p266_3 := h266c.2.2.2
                              linarith only [hlam, p266_0]
                        · linarith only [h154, h263, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                      · linarith only [h262, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h258, h261, h8, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h326 | h326
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h328 | h328
                          · linarith only [h258, h260, h328, hlam]
                          · rcases h1bigk with h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c | h330c
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h0, h154, h260, h327, h4, hlam, p330_2]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h259, hc01, hlam, hphi, ht0b, ht5b, p330_1, u5ehi8]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h0, h260, h327, h4, hlam, p330_2]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              rcases p330_3 (m.d 0 1) (by simp) with h335 | h335
                              · rcases p330_3 (m.d 1 2) (by simp) with h336 | h336
                                · linarith only [h0, h336, hlam]
                                · rcases p330_3 (m.d 1 3) (by simp) with h338 | h338
                                  · linarith only [h1, h338, hlam]
                                  · linarith only [h259, h338, hlam]
                              · linarith only [h335, hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h0, hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h8, hlam, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h154, hlam, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h256, hlam, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h1, hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              rcases p330_3 (m.d 0 1) (by simp) with h348 | h348
                              · rcases p330_3 (m.d 1 2) (by simp) with h349 | h349
                                · linarith only [h349, h8, hlam]
                                · rcases p330_3 (m.d 1 3) (by simp) with h351 | h351
                                  · rcases p330_3 (m.d 1 4) (by simp) with h352 | h352
                                    · linarith only [h258, h352, hlam]
                                    · linarith only [h154, h352, hlam]
                                  · linarith only [h351, h8, hlam]
                              · linarith only [h0, h348, hlam]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              rcases p330_3 (m.d 0 1) (by simp) with h358 | h358
                              · rcases p330_3 (m.d 1 2) (by simp) with h359 | h359
                                · linarith only [h359, h8, hlam]
                                · rcases p330_3 (m.d 1 3) (by simp) with h361 | h361
                                  · rcases p330_3 (m.d 1 4) (by simp) with h362 | h362
                                    · linarith only [h258, h362, hlam]
                                    · rcases p330_3 (m.d 1 5) (by simp) with h364 | h364
                                      · linarith only [h259, h364, hlam]
                                      · linarith only [h260, h364, hlam]
                                  · linarith only [h258, h361, hlam]
                              · linarith only [h2, h358, hlam]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p330_1, u5ehi6]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h2, hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h0, h260, h327, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h258, hlam, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h260, hlam, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h3, hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p330_1, u5elo1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h259, hlam, p330_0]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [h0, h260, h327, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p330_1]
                            · have p330_0 := h330c.1
                              have p330_1 := h330c.2.1
                              have p330_2 := h330c.2.2.1
                              have p330_3 := h330c.2.2.2
                              linarith only [hlam, p330_0]
                        · linarith only [h154, h327, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h326, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1, h259, h325, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · linarith only [h258, h259, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
                · linarith only [h1, h258, h384, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h387 | h387
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                          · rcases h1bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              rcases p391_3 (m.d 0 1) (by simp) with h393 | h393
                              · rcases p391_3 (m.d 1 2) (by simp) with h394 | h394
                                · linarith only [h394, hlam, p391_0]
                                · rcases p391_3 (m.d 1 3) (by simp) with h396 | h396
                                  · linarith only [h1, h396, hlam]
                                  · linarith only [h396, h8, hlam]
                              · linarith only [h393, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              rcases p391_3 (m.d 0 1) (by simp) with h400 | h400
                              · rcases p391_3 (m.d 1 2) (by simp) with h401 | h401
                                · linarith only [h0, h401, hlam]
                                · rcases p391_3 (m.d 1 3) (by simp) with h403 | h403
                                  · linarith only [h403, hlam, p391_0]
                                  · rcases p391_3 (m.d 1 4) (by simp) with h405 | h405
                                    · linarith only [h2, h405, hlam]
                                    · linarith only [h258, h405, hlam]
                              · linarith only [h400, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h386, hc01, hlam, hphi, ht0b, ht5b, p391_1, u5ehi9]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              rcases p391_3 (m.d 0 1) (by simp) with h410 | h410
                              · rcases p391_3 (m.d 1 2) (by simp) with h411 | h411
                                · linarith only [h0, h411, hlam]
                                · rcases p391_3 (m.d 1 3) (by simp) with h413 | h413
                                  · linarith only [h1, h413, hlam]
                                  · rcases p391_3 (m.d 1 4) (by simp) with h415 | h415
                                    · linarith only [h2, h415, hlam]
                                    · linarith only [h386, h415, hlam]
                              · linarith only [h410, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h0, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h8, hlam, p391_1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h154, hlam, p391_1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h256, hlam, p391_1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h1, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h384, h388, h5, hc12, hlam, hphi, ht23, ht34, ht45, p391_1, u5elo0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h258, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h384, hlam, p391_1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h2, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h258, h387, hc12, hc23, hlam, hphi, p391_1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h258, h387, h8, hc12, hc23, hlam, hphi, p391_1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h258, h387, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p391_1, u5ehi6]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h3, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p391_1, u5elo1]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h384, h388, h5, h8, hc12, hlam, hphi, ht23, ht34, ht45, p391_1, u5elo0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [h386, hlam, p391_0]
                            · have p391_0 := h391c.1
                              have p391_1 := h391c.2.1
                              have p391_2 := h391c.2.2.1
                              have p391_3 := h391c.2.2.2
                              linarith only [hlam, p391_0]
                          · linarith only [h258, h390, h7, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h258, h386, h387, h389, hlam]
                      · linarith only [h388, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
                      · linarith only [h1, h387, h442, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h442, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                          · linarith only [h154, h386, h445, h448, hc12, hc23, hlam, hphi]
                          · linarith only [h258, h448, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h154, h447, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                      · linarith only [h446, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h453 | h453
                      · linarith only [h1, h445, h453, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h453, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
        · rcases m.htr 1 2 4 (by decide) (by decide) with h457 | h457
          · rcases m.htr 1 2 5 (by decide) (by decide) with h458 | h458
            · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
              · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
                  · linarith only [h2, h461, h7, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                      · linarith only [h0, h456, h464, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h463, h464, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h463, h6, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h459, h460, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h459, h6, h7, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h456, h458, h5, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h4, h456, h457, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
          · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
            · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
              · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                  · linarith only [h2, h476, h7, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h479 | h479
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h480 | h480
                        · linarith only [h2, h472, h480, h7, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h482 | h482
                          · linarith only [h2, h472, h478, h482, h7, hlam]
                          · rcases h1bigk with h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c | h484c
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h473, h479, hc01, hlam, hphi, ht0b, ht5b, p484_1, u5ehi8]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h456, h473, h479, hc01, hlam, hphi, ht0b, ht5b, p484_1, u5ehi8]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              rcases p484_3 (m.d 0 1) (by simp) with h488 | h488
                              · rcases p484_3 (m.d 1 2) (by simp) with h489 | h489
                                · linarith only [h0, h489, hlam]
                                · linarith only [h472, h489, hlam]
                              · linarith only [h488, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              rcases p484_3 (m.d 0 1) (by simp) with h493 | h493
                              · rcases p484_3 (m.d 1 2) (by simp) with h494 | h494
                                · linarith only [h0, h494, hlam]
                                · linarith only [h473, h494, hlam]
                              · linarith only [h493, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h0, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h456, hlam, p484_1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              rcases p484_3 (m.d 0 1) (by simp) with h501 | h501
                              · rcases p484_3 (m.d 1 2) (by simp) with h502 | h502
                                · rcases p484_3 (m.d 1 3) (by simp) with h503 | h503
                                  · rcases p484_3 (m.d 1 4) (by simp) with h504 | h504
                                    · linarith only [h472, h504, hlam]
                                    · rcases p484_3 (m.d 1 5) (by simp) with h506 | h506
                                      · linarith only [h473, h506, hlam]
                                      · linarith only [h476, h506, hlam]
                                  · linarith only [h474, h503, hlam]
                                · linarith only [h472, h502, hlam]
                              · linarith only [h2, h501, hlam]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p484_1, u5ehi6]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h1, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h1, h472, h478, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p484_1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              rcases p484_3 (m.d 0 1) (by simp) with h516 | h516
                              · rcases p484_3 (m.d 1 2) (by simp) with h517 | h517
                                · linarith only [h456, h517, hlam]
                                · linarith only [h472, h517, hlam]
                              · linarith only [h2, h516, hlam]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h1, h473, h479, hc01, hlam, hphi, ht0b, ht5b, p484_1, u5ehi8]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h2, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h472, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h474, hlam, p484_1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h476, hlam, p484_1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h3, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h473, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h475, hlam, p484_0]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [h472, h478, hc34, hlam, hphi, ht45, p484_1, u5elo1]
                            · have p484_0 := h484c.1
                              have p484_1 := h484c.2.1
                              have p484_2 := h484c.2.2.1
                              have p484_3 := h484c.2.2.2
                              linarith only [hlam, p484_0]
                      · linarith only [h456, h473, h479, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h456, h473, h478, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h456, h473, h475, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h1, h456, h473, h474, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · linarith only [h472, h473, h5, h7, hc24, hlam, hphi, ht45, u5elo4]
          · linarith only [h4, h472, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h538 | h538
      · rcases m.htr 1 2 3 (by decide) (by decide) with h539 | h539
        · rcases m.htr 1 2 4 (by decide) (by decide) with h540 | h540
          · rcases m.htr 1 2 5 (by decide) (by decide) with h541 | h541
            · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
              · linarith only [h1, h542, h6, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h544 | h544
                · rcases m.htr 1 4 5 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h546 | h546
                    · linarith only [h1, h544, h546, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h548 | h548
                      · linarith only [h0, h540, h546, h548, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h1, h544, h548, h6, hc23, hc34, hlam, hphi]
                  · linarith only [h542, h544, h545, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                    · linarith only [h0, h539, h553, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                      · linarith only [h0, h539, h555, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                        · linarith only [h0, h540, h557, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
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
                              linarith only [h540, h552, h553, h557, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p560_1]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              rcases p560_3 (m.d 0 1) (by simp) with h563 | h563
                              · rcases p560_3 (m.d 1 2) (by simp) with h564 | h564
                                · linarith only [h0, h564, hlam]
                                · linarith only [h539, h564, hlam]
                              · linarith only [h563, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h552, h553, h557, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p560_1]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              rcases p560_3 (m.d 0 1) (by simp) with h569 | h569
                              · rcases p560_3 (m.d 1 2) (by simp) with h570 | h570
                                · linarith only [h0, h570, hlam]
                                · linarith only [h541, h570, hlam]
                              · linarith only [h569, hlam, p560_0]
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
                              rcases p560_3 (m.d 0 1) (by simp) with h576 | h576
                              · rcases p560_3 (m.d 1 2) (by simp) with h577 | h577
                                · rcases p560_3 (m.d 1 3) (by simp) with h578 | h578
                                  · linarith only [h539, h578, hlam]
                                  · rcases p560_3 (m.d 1 4) (by simp) with h580 | h580
                                    · linarith only [h540, h580, hlam]
                                    · linarith only [h542, h580, hlam]
                                · linarith only [h539, h577, hlam]
                              · linarith only [h1, h576, hlam]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h0, h552, h553, h557, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p560_1]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p560_1, u5ehi6]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h1, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h539, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h542, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h544, hlam, p560_1]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h2, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h540, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              rcases p560_3 (m.d 0 1) (by simp) with h594 | h594
                              · rcases p560_3 (m.d 1 2) (by simp) with h595 | h595
                                · rcases p560_3 (m.d 1 3) (by simp) with h596 | h596
                                  · linarith only [h542, h596, hlam]
                                  · rcases p560_3 (m.d 1 4) (by simp) with h598 | h598
                                    · rcases p560_3 (m.d 1 5) (by simp) with h599 | h599
                                      · linarith only [h552, h599, hlam]
                                      · linarith only [h544, h599, hlam]
                                    · linarith only [h542, h598, hlam]
                                · linarith only [h539, h595, hlam]
                              · linarith only [h1, h594, hlam]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h2, h552, h553, h557, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p560_1]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h3, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h541, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [hc13, hlam, hphi, ht34, ht45, p560_1, u5elo1]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [h552, hlam, p560_0]
                            · have p560_0 := h560c.1
                              have p560_1 := h560c.2.1
                              have p560_2 := h560c.2.2.1
                              have p560_3 := h560c.2.2.2
                              linarith only [hlam, p560_0]
                          · linarith only [h559, h6, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                    · linarith only [h1, h539, h6, h613, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                      · linarith only [h0, h539, h615, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                        · linarith only [h540, h552, h617, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h619 | h619
                          · rcases h1bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h541, hc01, hlam, hphi, ht0b, ht5b, p620_1, u5ehi7]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 1) (by simp) with h623 | h623
                              · rcases p620_3 (m.d 1 2) (by simp) with h624 | h624
                                · linarith only [h0, h624, hlam]
                                · linarith only [h539, h624, hlam]
                              · linarith only [h623, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 1) (by simp) with h628 | h628
                              · rcases p620_3 (m.d 1 2) (by simp) with h629 | h629
                                · linarith only [h0, h629, hlam]
                                · linarith only [h540, h629, hlam]
                              · linarith only [h628, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 1) (by simp) with h633 | h633
                              · rcases p620_3 (m.d 1 2) (by simp) with h634 | h634
                                · linarith only [h0, h634, hlam]
                                · linarith only [h541, h634, hlam]
                              · linarith only [h633, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h0, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 1) (by simp) with h640 | h640
                              · rcases p620_3 (m.d 1 2) (by simp) with h641 | h641
                                · rcases p620_3 (m.d 1 3) (by simp) with h642 | h642
                                  · linarith only [h539, h642, hlam]
                                  · rcases p620_3 (m.d 1 4) (by simp) with h644 | h644
                                    · linarith only [h540, h644, hlam]
                                    · linarith only [h542, h644, hlam]
                                · linarith only [h539, h641, hlam]
                              · linarith only [h1, h640, hlam]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 1) (by simp) with h649 | h649
                              · rcases p620_3 (m.d 1 2) (by simp) with h650 | h650
                                · rcases p620_3 (m.d 1 3) (by simp) with h651 | h651
                                  · linarith only [h539, h651, hlam]
                                  · rcases p620_3 (m.d 1 4) (by simp) with h653 | h653
                                    · linarith only [h540, h653, hlam]
                                    · rcases p620_3 (m.d 1 5) (by simp) with h655 | h655
                                      · linarith only [h541, h655, hlam]
                                      · linarith only [h552, h655, hlam]
                                · linarith only [h540, h650, hlam]
                              · linarith only [h2, h649, hlam]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h0, h541, hc01, hlam, hphi, ht0b, ht5b, p620_1, u5ehi7]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h1, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h539, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h542, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h544, hlam, p620_1]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h2, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h540, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h538, h552, hc13, hlam, hphi, ht34, ht45, p620_1, u5elo0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h552, hlam, p620_1]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h3, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h541, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h539, hc23, hlam, hphi, ht34, ht45, p620_1, u5elo1]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h538, h552, hc14, hlam, hphi, ht45, p620_1, u5elo0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                          · linarith only [h538, h6, h619, hlam]
            · linarith only [h5, h539, h541, hc23, hlam, hphi, ht34, ht45, u5elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
            · linarith only [h0, h4, h540, h678, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · linarith only [h5, h539, h678, hc23, hlam, hphi, ht34, ht45, u5elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h681 | h681
          · rcases m.htr 1 2 5 (by decide) (by decide) with h682 | h682
            · rcases m.htr 1 3 4 (by decide) (by decide) with h683 | h683
              · linarith only [h1, h6, h683, hlam]
              · linarith only [h539, h681, h683, hlam]
            · linarith only [h5, h681, h682, hc24, hlam, hphi, ht45, u5elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h687 | h687
            · linarith only [h0, h4, h681, h687, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h689 | h689
              · linarith only [h1, h6, h689, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h691 | h691
                · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h693 | h693
                    · linarith only [h1, h6, h691, h693, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h696 | h696
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h697 | h697
                          · rcases h1bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              rcases p698_3 (m.d 0 1) (by simp) with h700 | h700
                              · rcases p698_3 (m.d 1 2) (by simp) with h701 | h701
                                · linarith only [h701, hlam, p698_0]
                                · rcases p698_3 (m.d 1 3) (by simp) with h703 | h703
                                  · linarith only [h1, h703, hlam]
                                  · linarith only [h539, h703, hlam]
                              · linarith only [h700, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h691, h697, hc01, hlam, hphi, ht0b, ht5b, p698_1, u5ehi9]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h689, h691, h697, hc01, hlam, hphi, ht0b, ht5b, p698_1, u5ehi9]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              rcases p698_3 (m.d 0 1) (by simp) with h709 | h709
                              · rcases p698_3 (m.d 1 2) (by simp) with h710 | h710
                                · linarith only [h0, h710, hlam]
                                · rcases p698_3 (m.d 1 3) (by simp) with h712 | h712
                                  · linarith only [h1, h712, hlam]
                                  · linarith only [h691, h712, hlam]
                              · linarith only [h709, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h0, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h539, hlam, p698_1]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h681, hlam, p698_1]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h687, hlam, p698_1]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h1, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h1, h6, hc12, hc34, hlam, hphi, ht23, p698_1]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h689, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h1, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p698_1, u5ehi6]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h2, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              rcases p698_3 (m.d 0 1) (by simp) with h727 | h727
                              · rcases p698_3 (m.d 1 2) (by simp) with h728 | h728
                                · linarith only [h681, h728, hlam]
                                · rcases p698_3 (m.d 1 3) (by simp) with h730 | h730
                                  · linarith only [h689, h730, hlam]
                                  · linarith only [h539, h730, hlam]
                              · linarith only [h0, h727, hlam]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h0, h4, h681, h691, h697, hc01, hlam, hphi, ht0b, ht5b, p698_1, u5ehi9]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h0, h4, h681, h691, h697, hc01, hlam, hphi, ht0b, ht5b, p698_1, u5ehi9]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h3, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p698_1, u5elo1]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h691, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [h692, hlam, p698_0]
                            · have p698_0 := h698c.1
                              have p698_1 := h698c.2.1
                              have p698_2 := h698c.2.2.1
                              have p698_3 := h698c.2.2.2
                              linarith only [hlam, p698_0]
                          · linarith only [h1, h6, h691, h697, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                        · linarith only [h681, h692, h696, hlam]
                      · linarith only [h1, h6, h691, h695, hc23, hc34, hlam, hphi]
                  · linarith only [h538, h689, h691, h692, hlam, hphi, u5ehi8, u5elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h746 | h746
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h747 | h747
                    · linarith only [h4, h6, h747, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h749 | h749
                      · linarith only [h539, h691, h747, h749, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h539, h749, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                    · linarith only [h538, h6, h681, h746, h752, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h754 | h754
                      · linarith only [h539, h691, h752, h754, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h539, h754, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
        · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
          · rcases m.htr 1 2 5 (by decide) (by decide) with h759 | h759
            · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
              · linarith only [h1, h538, h6, h760, hc34, hlam, hphi, ht45, u5elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                · linarith only [h1, h538, h6, h762, hlam, hphi, u5ehi8, u5elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                  · linarith only [h2, h538, h764, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h766 | h766
                    · linarith only [h0, h6, h757, h766, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h768 | h768
                      · linarith only [h757, h762, h768, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                        · linarith only [h2, h538, h758, h770, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h772 | h772
                          · rcases h1bigk with h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h759, hc01, hlam, hphi, ht0b, ht5b, p773_1, u5ehi7]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              rcases p773_3 (m.d 0 1) (by simp) with h776 | h776
                              · rcases p773_3 (m.d 1 2) (by simp) with h777 | h777
                                · linarith only [h0, h777, hlam]
                                · linarith only [h757, h777, hlam]
                              · linarith only [h776, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              rcases p773_3 (m.d 0 1) (by simp) with h781 | h781
                              · rcases p773_3 (m.d 1 2) (by simp) with h782 | h782
                                · linarith only [h0, h782, hlam]
                                · linarith only [h758, h782, hlam]
                              · linarith only [h781, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              rcases p773_3 (m.d 0 1) (by simp) with h786 | h786
                              · rcases p773_3 (m.d 1 2) (by simp) with h787 | h787
                                · linarith only [h0, h787, hlam]
                                · linarith only [h759, h787, hlam]
                              · linarith only [h786, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h0, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              rcases p773_3 (m.d 0 1) (by simp) with h793 | h793
                              · rcases p773_3 (m.d 1 2) (by simp) with h794 | h794
                                · rcases p773_3 (m.d 1 3) (by simp) with h795 | h795
                                  · linarith only [h757, h795, hlam]
                                  · rcases p773_3 (m.d 1 4) (by simp) with h797 | h797
                                    · linarith only [h758, h797, hlam]
                                    · linarith only [h760, h797, hlam]
                                · linarith only [h757, h794, hlam]
                              · linarith only [h1, h793, hlam]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              rcases p773_3 (m.d 0 1) (by simp) with h802 | h802
                              · rcases p773_3 (m.d 1 2) (by simp) with h803 | h803
                                · rcases p773_3 (m.d 1 3) (by simp) with h804 | h804
                                  · linarith only [h757, h804, hlam]
                                  · rcases p773_3 (m.d 1 4) (by simp) with h806 | h806
                                    · linarith only [h758, h806, hlam]
                                    · rcases p773_3 (m.d 1 5) (by simp) with h808 | h808
                                      · linarith only [h759, h808, hlam]
                                      · linarith only [h764, h808, hlam]
                                · linarith only [h758, h803, hlam]
                              · linarith only [h2, h802, hlam]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p773_1, u5ehi6]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h1, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h757, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h760, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h762, hlam, p773_1]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h2, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h758, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h2, h538, h772, hc13, hlam, hphi, ht34, ht45, p773_1, u5elo3]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h764, hlam, p773_1]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h3, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h759, hlam, p773_0]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h757, hc23, hlam, hphi, ht34, ht45, p773_1, u5elo1]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [h3, h538, h772, hc14, hlam, hphi, ht45, p773_1, u5elo3]
                            · have p773_0 := h773c.1
                              have p773_1 := h773c.2.1
                              have p773_2 := h773c.2.2.1
                              have p773_3 := h773c.2.2.2
                              linarith only [hlam, p773_0]
                          · linarith only [h1, h6, h757, h772, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h5, h538, h757, h759, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h4, h538, h757, h758, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h832 | h832
          · linarith only [h1, h538, h6, h757, h832, hc24, hlam, hphi, ht45, u5elo4]
          · linarith only [h4, h538, h832, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
  · linarith only [h4, h5, hc24, hlam, hphi, ht45, u5elo2]

end R2N4
