import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h11, h14, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h11, h13, h16, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h11, h18, h6, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h11, h13, h18, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h10, h11, h13, h21, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h10, h11, h23, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h11, h13, h25, h6, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h1, h21, h27, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h10, h11, h23, h29, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                            · linarith only [h10, h11, h25, h29, h31, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                rcases p33_3 (m.d 0 1) (by simp) with h35 | h35
                                · rcases p33_3 (m.d 1 2) (by simp) with h36 | h36
                                  · linarith only [h36, hlam, p33_0]
                                  · rcases p33_3 (m.d 1 3) (by simp) with h38 | h38
                                    · linarith only [h1, h38, hlam]
                                    · rcases p33_3 (m.d 1 4) (by simp) with h40 | h40
                                      · linarith only [h2, h40, hlam]
                                      · rcases p33_3 (m.d 1 5) (by simp) with h42 | h42
                                        · linarith only [h3, h42, hlam]
                                        · linarith only [h11, h42, hlam]
                                · linarith only [h35, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h0, h13, h31, h4, h7, h8, hlam, p33_2]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                rcases p33_3 (m.d 0 1) (by simp) with h47 | h47
                                · rcases p33_3 (m.d 1 2) (by simp) with h48 | h48
                                  · linarith only [h0, h48, hlam]
                                  · linarith only [h10, h48, hlam]
                                · linarith only [h47, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p33_1, u5ehi1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h0, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h0, h11, h27, h31, h4, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h0, h11, h27, h31, h4, h7, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h11, hlam, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h1, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h9, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h13, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h21, hlam, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h2, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h10, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h0, h10, h11, h27, h31, h4, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h23, hlam, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h3, hlam, p33_0]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [h10, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p33_1]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                rcases p33_3 (m.d 0 1) (by simp) with h70 | h70
                                · rcases p33_3 (m.d 1 2) (by simp) with h71 | h71
                                  · linarith only [h11, h71, hlam]
                                  · linarith only [h71, h9, hlam]
                                · linarith only [h1, h70, hlam]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                rcases p33_3 (m.d 0 1) (by simp) with h75 | h75
                                · rcases p33_3 (m.d 1 2) (by simp) with h76 | h76
                                  · linarith only [h11, h76, hlam]
                                  · linarith only [h10, h76, hlam]
                                · linarith only [h2, h75, hlam]
                              · have p33_0 := h33c.1
                                have p33_1 := h33c.2.1
                                have p33_2 := h33c.2.2.1
                                have p33_3 := h33c.2.2.2
                                linarith only [hlam, p33_0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
              · linarith only [h10, h81, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                · linarith only [h10, h83, h9, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                  · linarith only [h0, h10, h5, h85, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                    · linarith only [h2, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                      · linarith only [h0, h10, h4, h7, h8, h87, h89, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                        · linarith only [h0, h10, h4, h7, h8, h85, h87, h9, h91, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                          · linarith only [h10, h87, h89, h9, h93, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h10, h4, h7, h8, h9, h93, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
            · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
              · linarith only [h9, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                  · linarith only [h1, h100, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                    · linarith only [h0, h102, h4, h9, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                        · linarith only [h0, h105, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h100, h102, h105, h107, h9, h96, hc13, hc35, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                            · linarith only [h104, h105, h107, h109, h9, h96, hlam]
                            · linarith only [h0, h105, h109, h4, h7, h8, h9, h96, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h104, h4, h7, h9, h96, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h9, h96, h99, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
              · linarith only [h114, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
                · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h1, h117, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h119, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                        · linarith only [h0, h122, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                          · linarith only [h119, h121, h122, h124, h96, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                            · linarith only [h116, h122, h124, h126, h9, h96, hc12, hc35, hlam, hphi, ht23]
                            · rcases h1bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h122, h126, h4, h7, h8, h9, hlam, p128_2]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h131 | h131
                                · rcases p128_3 (m.d 1 2) (by simp) with h132 | h132
                                  · linarith only [h0, h132, hlam]
                                  · rcases p128_3 (m.d 1 3) (by simp) with h134 | h134
                                    · linarith only [h134, hlam, p128_0]
                                    · rcases p128_3 (m.d 1 4) (by simp) with h136 | h136
                                      · linarith only [h136, h2, hlam]
                                      · rcases p128_3 (m.d 1 5) (by simp) with h138 | h138
                                        · linarith only [h138, h3, hlam]
                                        · linarith only [h117, h138, hlam]
                                · linarith only [h131, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h142 | h142
                                · rcases p128_3 (m.d 1 2) (by simp) with h143 | h143
                                  · linarith only [h0, h143, hlam]
                                  · rcases p128_3 (m.d 1 3) (by simp) with h145 | h145
                                    · linarith only [h1, h145, hlam]
                                    · linarith only [h116, h145, hlam]
                                · linarith only [h142, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p128_1, u5ehi1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h9, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h96, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h114, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h1, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h122, h126, h4, h7, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h122, h126, h4, h7, h8, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h117, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h2, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h121, h122, h126, h4, h7, h8, h96, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h116, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h119, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h3, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h166 | h166
                                · rcases p128_3 (m.d 1 2) (by simp) with h167 | h167
                                  · linarith only [h114, h167, hlam]
                                  · rcases p128_3 (m.d 1 3) (by simp) with h169 | h169
                                    · linarith only [h117, h169, hlam]
                                    · linarith only [h169, h9, hlam]
                                · linarith only [h0, h166, hlam]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h116, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h174 | h174
                                · rcases p128_3 (m.d 1 2) (by simp) with h175 | h175
                                  · linarith only [h114, h175, hlam]
                                  · rcases p128_3 (m.d 1 3) (by simp) with h177 | h177
                                    · linarith only [h117, h177, hlam]
                                    · linarith only [h116, h177, hlam]
                                · linarith only [h174, h2, hlam]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                      · linarith only [h116, h121, h9, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                  · linarith only [h116, h183, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                    · linarith only [h185, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                        · linarith only [h0, h183, h188, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h116, h187, h188, h9, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                        · linarith only [h187, h191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h0, h193, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h195 | h195
                            · linarith only [h0, h187, h193, h195, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h187, h195, h9, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
          · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
            · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
              · linarith only [h0, h200, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                · rcases m.htr 1 3 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h1, h203, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                    · linarith only [h2, h205, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                      · linarith only [h0, h198, h200, h207, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h198, h200, h202, h207, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
                  · linarith only [h202, h210, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                    · linarith only [h2, h202, h212, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                      · linarith only [h198, h202, h214, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
                        · linarith only [h199, h200, h210, h214, h216, h6, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                          · linarith only [h199, h200, h218, h6, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                            · linarith only [h199, h200, h214, h220, h6, h8, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                rcases p222_3 (m.d 0 1) (by simp) with h224 | h224
                                · rcases p222_3 (m.d 1 2) (by simp) with h225 | h225
                                  · linarith only [h225, hlam, p222_0]
                                  · rcases p222_3 (m.d 1 3) (by simp) with h227 | h227
                                    · linarith only [h1, h227, hlam]
                                    · rcases p222_3 (m.d 1 4) (by simp) with h229 | h229
                                      · linarith only [h2, h229, hlam]
                                      · rcases p222_3 (m.d 1 5) (by simp) with h231 | h231
                                        · linarith only [h231, h3, hlam]
                                        · linarith only [h200, h231, hlam]
                                · linarith only [h224, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                rcases p222_3 (m.d 0 1) (by simp) with h235 | h235
                                · rcases p222_3 (m.d 1 2) (by simp) with h236 | h236
                                  · linarith only [h0, h236, hlam]
                                  · linarith only [h198, h236, hlam]
                                · linarith only [h235, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                rcases p222_3 (m.d 0 1) (by simp) with h240 | h240
                                · rcases p222_3 (m.d 1 2) (by simp) with h241 | h241
                                  · linarith only [h0, h241, hlam]
                                  · linarith only [h199, h241, hlam]
                                · linarith only [h240, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p222_1, u5ehi1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h0, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h200, h216, hc13, hc35, hlam, hphi, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h0, h200, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h200, hlam, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h1, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h198, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h202, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h210, hlam, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h2, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h199, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h198, h2, h8, hc23, hc45, hlam, hphi, ht34, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h212, hlam, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h3, hlam, p222_0]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [h198, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                rcases p222_3 (m.d 0 1) (by simp) with h263 | h263
                                · rcases p222_3 (m.d 1 2) (by simp) with h264 | h264
                                  · linarith only [h200, h264, hlam]
                                  · linarith only [h198, h264, hlam]
                                · linarith only [h1, h263, hlam]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                rcases p222_3 (m.d 0 1) (by simp) with h268 | h268
                                · rcases p222_3 (m.d 1 2) (by simp) with h269 | h269
                                  · linarith only [h200, h269, hlam]
                                  · linarith only [h199, h269, hlam]
                                · linarith only [h2, h268, hlam]
                              · have p222_0 := h222c.1
                                have p222_1 := h222c.2.1
                                have p222_2 := h222c.2.2.1
                                have p222_3 := h222c.2.2.2
                                linarith only [hlam, p222_0]
            · linarith only [h198, h199, h5, h8, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
            · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
              · linarith only [h198, h276, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                  · linarith only [h1, h279, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                    · linarith only [h2, h281, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                        · linarith only [h0, h284, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h286 | h286
                          · linarith only [h0, h286, h5, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                            · linarith only [h198, h275, h283, h284, h288, h6, h8, hlam]
                            · linarith only [h198, h275, h283, h284, h288, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h198, h275, h283, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h198, h275, h278, h7, h8, hc24, hc45, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
              · linarith only [h275, h293, h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                  · linarith only [h1, h296, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                    · linarith only [h275, h298, h5, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                        · linarith only [h0, h301, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                          · linarith only [h303, h5, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h275, h295, h305, h5, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 1) (by simp) with h309 | h309
                                · rcases p307_3 (m.d 1 2) (by simp) with h310 | h310
                                  · linarith only [h310, hlam, p307_0]
                                  · rcases p307_3 (m.d 1 3) (by simp) with h312 | h312
                                    · linarith only [h1, h312, hlam]
                                    · linarith only [h198, h312, hlam]
                                · linarith only [h309, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 1) (by simp) with h316 | h316
                                · rcases p307_3 (m.d 1 2) (by simp) with h317 | h317
                                  · linarith only [h0, h317, hlam]
                                  · rcases p307_3 (m.d 1 3) (by simp) with h319 | h319
                                    · linarith only [h319, hlam, p307_0]
                                    · rcases p307_3 (m.d 1 4) (by simp) with h321 | h321
                                      · linarith only [h2, h321, hlam]
                                      · rcases p307_3 (m.d 1 5) (by simp) with h323 | h323
                                        · linarith only [h3, h323, hlam]
                                        · linarith only [h296, h323, hlam]
                                · linarith only [h316, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 1) (by simp) with h327 | h327
                                · rcases p307_3 (m.d 1 2) (by simp) with h328 | h328
                                  · linarith only [h0, h328, hlam]
                                  · rcases p307_3 (m.d 1 3) (by simp) with h330 | h330
                                    · linarith only [h1, h330, hlam]
                                    · linarith only [h295, h330, hlam]
                                · linarith only [h327, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p307_1, u5ehi1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h198, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h275, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h293, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h198, h301, h305, hc12, hc45, hlam, hphi, ht23, ht34, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h198, h301, h305, hc14, hc45, hlam, hphi, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h296, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h295, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h298, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h3, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 1) (by simp) with h351 | h351
                                · rcases p307_3 (m.d 1 2) (by simp) with h352 | h352
                                  · linarith only [h293, h352, hlam]
                                  · rcases p307_3 (m.d 1 3) (by simp) with h354 | h354
                                    · linarith only [h296, h354, hlam]
                                    · linarith only [h198, h354, hlam]
                                · linarith only [h0, h351, hlam]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, h293, h295, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                rcases p307_3 (m.d 0 1) (by simp) with h359 | h359
                                · rcases p307_3 (m.d 1 2) (by simp) with h360 | h360
                                  · linarith only [h293, h360, hlam]
                                  · rcases p307_3 (m.d 1 3) (by simp) with h362 | h362
                                    · linarith only [h296, h362, hlam]
                                    · linarith only [h295, h362, hlam]
                                · linarith only [h2, h359, hlam]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                      · linarith only [h1, h198, h295, h300, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h295, h368, h7, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h2, h295, h370, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h373 | h373
                        · linarith only [h0, h368, h373, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h198, h295, h372, h373, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h198, h372, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h377 | h377
        · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
          · rcases m.htr 1 2 4 (by decide) (by decide) with h379 | h379
            · rcases m.htr 1 2 5 (by decide) (by decide) with h380 | h380
              · linarith only [h0, h380, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h382 | h382
                · linarith only [h1, h382, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
                  · linarith only [h0, h379, h380, h382, h384, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
                    · linarith only [h0, h379, h380, h386, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                      · linarith only [h377, h386, h388, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h390 | h390
                        · linarith only [h0, h379, h380, h384, h388, h390, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h392 | h392
                          · linarith only [h0, h379, h380, h386, h392, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h377, h379, h380, h388, h392, h7, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h395 | h395
              · linarith only [h0, h379, h395, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
                · linarith only [h0, h378, h379, h397, h5, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h0, h378, h379, h399, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                    · linarith only [h2, h401, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h377, h378, h379, h401, h7, hc23, hc34, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
            · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
              · linarith only [h378, h4, h405, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                · linarith only [h378, h4, h407, h7, hlam]
                · linarith only [h378, h404, h407, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h410 | h410
              · linarith only [h378, h4, h410, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                · linarith only [h1, h378, h4, h412, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
                  · linarith only [h1, h414, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
                    · linarith only [h0, h404, h416, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                      · linarith only [h4, h418, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                        · linarith only [h4, h414, h420, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h422 | h422
                          · linarith only [h0, h416, h422, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h377, h404, h422, h7, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
          · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
            · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
              · linarith only [h0, h427, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                · linarith only [h1, h429, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                  · linarith only [h1, h431, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h433 | h433
                    · linarith only [h0, h377, h426, h427, h433, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                      · linarith only [h1, h425, h435, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
                        · linarith only [h0, h426, h427, h431, h435, h437, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                          · linarith only [h377, h426, h427, h439, h6, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h441 | h441
                            · linarith only [h377, h426, h427, h435, h441, h6, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c | h443c
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                rcases p443_3 (m.d 0 1) (by simp) with h445 | h445
                                · rcases p443_3 (m.d 1 2) (by simp) with h446 | h446
                                  · linarith only [h446, hlam, p443_0]
                                  · rcases p443_3 (m.d 1 3) (by simp) with h448 | h448
                                    · linarith only [h1, h448, hlam]
                                    · rcases p443_3 (m.d 1 4) (by simp) with h450 | h450
                                      · linarith only [h2, h450, hlam]
                                      · rcases p443_3 (m.d 1 5) (by simp) with h452 | h452
                                        · linarith only [h3, h452, hlam]
                                        · linarith only [h427, h452, hlam]
                                · linarith only [h445, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                rcases p443_3 (m.d 0 1) (by simp) with h456 | h456
                                · rcases p443_3 (m.d 1 2) (by simp) with h457 | h457
                                  · linarith only [h0, h457, hlam]
                                  · linarith only [h425, h457, hlam]
                                · linarith only [h456, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                rcases p443_3 (m.d 0 1) (by simp) with h461 | h461
                                · rcases p443_3 (m.d 1 2) (by simp) with h462 | h462
                                  · linarith only [h0, h462, hlam]
                                  · linarith only [h426, h462, hlam]
                                · linarith only [h461, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p443_1, u5ehi1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h0, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h427, h6, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h0, h427, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h427, hlam, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h1, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h425, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h429, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h431, hlam, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h2, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h426, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h2, h425, h441, h7, hc23, hc45, hlam, hphi, ht34, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h433, hlam, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h3, hlam, p443_0]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [h3, h425, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p443_1]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                rcases p443_3 (m.d 0 1) (by simp) with h484 | h484
                                · rcases p443_3 (m.d 1 2) (by simp) with h485 | h485
                                  · linarith only [h427, h485, hlam]
                                  · linarith only [h425, h485, hlam]
                                · linarith only [h1, h484, hlam]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                rcases p443_3 (m.d 0 1) (by simp) with h489 | h489
                                · rcases p443_3 (m.d 1 2) (by simp) with h490 | h490
                                  · linarith only [h427, h490, hlam]
                                  · linarith only [h426, h490, hlam]
                                · linarith only [h2, h489, hlam]
                              · have p443_0 := h443c.1
                                have p443_1 := h443c.2.1
                                have p443_2 := h443c.2.2.1
                                have p443_3 := h443c.2.2.2
                                linarith only [hlam, p443_0]
            · linarith only [h377, h425, h426, h5, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
            · linarith only [h377, h4, h425, h496, h7, hc24, hc45, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h498 | h498
              · linarith only [h377, h4, h425, h498, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h500 | h500
                · linarith only [h4, h425, h500, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                  · linarith only [h1, h502, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
                    · linarith only [h377, h4, h425, h496, h504, h7, hc12, hc24, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                      · linarith only [h4, h506, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                        · linarith only [h4, h502, h508, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h510 | h510
                          · linarith only [h377, h5, h510, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h512 | h512
                            · linarith only [h377, h4, h425, h512, h7, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h4, h425, h512, h7, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h515 | h515
      · rcases m.htr 0 4 5 (by decide) (by decide) with h516 | h516
        · linarith only [h4, h515, h516, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h518 | h518
          · rcases m.htr 1 2 4 (by decide) (by decide) with h519 | h519
            · rcases m.htr 1 2 5 (by decide) (by decide) with h520 | h520
              · linarith only [h0, h520, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
                · rcases m.htr 1 3 5 (by decide) (by decide) with h523 | h523
                  · linarith only [h1, h523, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h525 | h525
                    · linarith only [h2, h516, h525, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h527 | h527
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h528 | h528
                        · linarith only [h0, h518, h523, h528, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h530 | h530
                          · linarith only [h0, h516, h518, h527, h528, h530, h6, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h518, h527, h530, h6, hc34, hc45, hlam, hphi]
                      · linarith only [h522, h523, h527, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h534 | h534
                  · linarith only [h4, h515, h522, h534, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
                    · linarith only [h4, h515, h522, h536, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                      · linarith only [h4, h522, h538, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                        · linarith only [h515, h518, h522, h534, h540, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h4, h515, h518, h522, h540, h6, hc23, hc35, hlam, hphi]
            · linarith only [h5, h519, h6, hc12, hc25, hlam, hphi]
          · linarith only [h4, h518, h6, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h545 | h545
        · linarith only [h5, h545, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h547 | h547
          · rcases m.htr 1 2 4 (by decide) (by decide) with h548 | h548
            · rcases m.htr 1 2 5 (by decide) (by decide) with h549 | h549
              · linarith only [h0, h549, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h551 | h551
                · linarith only [h1, h515, h551, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h553 | h553
                  · linarith only [h1, h515, h553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h555 | h555
                    · linarith only [h2, h545, h555, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h557 | h557
                      · linarith only [h0, h515, h547, h557, h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
                        · linarith only [h1, h547, h553, h559, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h561 | h561
                          · linarith only [h0, h548, h561, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h563 | h563
                            · linarith only [h0, h548, h557, h561, h563, h6, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 1) (by simp) with h567 | h567
                                · rcases p565_3 (m.d 1 2) (by simp) with h568 | h568
                                  · linarith only [h568, hlam, p565_0]
                                  · rcases p565_3 (m.d 1 3) (by simp) with h570 | h570
                                    · linarith only [h1, h570, hlam]
                                    · rcases p565_3 (m.d 1 4) (by simp) with h572 | h572
                                      · linarith only [h2, h572, hlam]
                                      · rcases p565_3 (m.d 1 5) (by simp) with h574 | h574
                                        · linarith only [h3, h574, hlam]
                                        · linarith only [h549, h574, hlam]
                                · linarith only [h567, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 1) (by simp) with h578 | h578
                                · rcases p565_3 (m.d 1 2) (by simp) with h579 | h579
                                  · linarith only [h0, h579, hlam]
                                  · linarith only [h547, h579, hlam]
                                · linarith only [h578, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 1) (by simp) with h583 | h583
                                · rcases p565_3 (m.d 1 2) (by simp) with h584 | h584
                                  · linarith only [h0, h584, hlam]
                                  · linarith only [h548, h584, hlam]
                                · linarith only [h583, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht5b, p565_1, u5ehi1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h0, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h0, h547, h559, h6, hc23, hc35, hlam, hphi, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h0, h548, h557, h559, h6, hc23, hc35, hlam, hphi, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h549, hlam, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h1, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h547, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h551, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h553, hlam, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h2, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h548, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h2, h5, h547, h559, h6, hc23, hc35, hlam, hphi, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h555, hlam, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h3, hlam, p565_0]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [h3, h547, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p565_1]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 1) (by simp) with h606 | h606
                                · rcases p565_3 (m.d 1 2) (by simp) with h607 | h607
                                  · linarith only [h549, h607, hlam]
                                  · linarith only [h547, h607, hlam]
                                · linarith only [h1, h606, hlam]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                rcases p565_3 (m.d 0 1) (by simp) with h611 | h611
                                · rcases p565_3 (m.d 1 2) (by simp) with h612 | h612
                                  · linarith only [h549, h612, hlam]
                                  · linarith only [h548, h612, hlam]
                                · linarith only [h2, h611, hlam]
                              · have p565_0 := h565c.1
                                have p565_1 := h565c.2.1
                                have p565_2 := h565c.2.2.1
                                have p565_3 := h565c.2.2.2
                                linarith only [hlam, p565_0]
            · linarith only [h5, h548, h6, hc12, hc25, hlam, hphi]
          · linarith only [h4, h547, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h619 | h619
    · linarith only [h5, h619, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h621 | h621
      · linarith only [h4, h5, h621, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h623 | h623
        · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
          · rcases m.htr 1 2 4 (by decide) (by decide) with h625 | h625
            · linarith only [h0, h5, h625, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
              · linarith only [h0, h619, h627, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h629 | h629
                · linarith only [h1, h621, h629, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h631 | h631
                  · linarith only [h1, h4, h5, h631, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h633 | h633
                    · linarith only [h2, h633, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h621, h623, h624, h625, h633, hc23, hc34, hlam, hphi]
          · linarith only [h4, h5, h624, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
          · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
            · linarith only [h0, h5, h638, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h640 | h640
              · linarith only [h0, h3, h5, h619, h640, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h642 | h642
                · linarith only [h1, h621, h642, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h644 | h644
                  · linarith only [h1, h4, h5, h623, h644, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h646 | h646
                    · linarith only [h0, h2, h5, h623, h637, h646, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h648 | h648
                      · linarith only [h0, h1, h619, h621, h637, h648, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
                        · linarith only [h1, h637, h644, h650, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h652 | h652
                          · linarith only [h0, h5, h623, h637, h648, h652, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h5, h637, h652, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h637, hc12, hc24, hlam, hphi]

end R2N4
