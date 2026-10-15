import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
              · linarith only [h12, h7, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h11, h12, h14, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h12, h17, h7, h9, hlam]
                    · linarith only [h0, h16, h17, h4, h6, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h11, h12, h16, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h11, h21, h8, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h21, h23, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h11, h21, h25, h4, h6, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h1, h21, h27, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h27, h29, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h25, h29, h31, h4, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                    · linarith only [h42, h9, hlam]
                            · linarith only [h35, hlam, p33_0]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            rcases p33_3 (m.d 0 1) (by simp) with h46 | h46
                            · rcases p33_3 (m.d 1 2) (by simp) with h47 | h47
                              · linarith only [h0, h47, hlam]
                              · linarith only [h47, h7, hlam]
                            · linarith only [h46, hlam, p33_0]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            rcases p33_3 (m.d 0 1) (by simp) with h51 | h51
                            · rcases p33_3 (m.d 1 2) (by simp) with h52 | h52
                              · linarith only [h0, h52, hlam]
                              · linarith only [h52, h8, hlam]
                            · linarith only [h51, hlam, p33_0]
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
                            linarith only [h0, h27, h4, h6, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33_1]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [h0, h25, h27, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33_1]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [h9, hlam, p33_0]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [h1, hlam, p33_0]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [h7, hlam, p33_1]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [hlam, p33_0]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [h11, hlam, p33_1]
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
                            linarith only [h8, hlam, p33_1]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [h11, h31, h7, hc23, hc45, hlam, hphi, ht34, p33_1]
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
                            linarith only [h3, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33_1]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            rcases p33_3 (m.d 0 1) (by simp) with h74 | h74
                            · rcases p33_3 (m.d 1 2) (by simp) with h75 | h75
                              · linarith only [h75, h9, hlam]
                              · linarith only [h7, h75, hlam]
                            · linarith only [h1, h74, hlam]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            rcases p33_3 (m.d 0 1) (by simp) with h79 | h79
                            · rcases p33_3 (m.d 1 2) (by simp) with h80 | h80
                              · linarith only [h80, h9, hlam]
                              · linarith only [h8, h80, hlam]
                            · linarith only [h2, h79, hlam]
                          · have p33_0 := h33c.1
                            have p33_1 := h33c.2.1
                            have p33_2 := h33c.2.2.1
                            have p33_3 := h33c.2.2.2
                            linarith only [hlam, p33_0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
          · linarith only [h8, h85, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
            · linarith only [h7, h8, h87, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
              · linarith only [h0, h4, h5, h87, h89, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                · linarith only [h0, h4, h5, h87, h91, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                  · linarith only [h7, h8, h87, h93, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                    · linarith only [h5, h7, h8, h89, h93, h95, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                      · linarith only [h0, h4, h5, h93, h97, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h7, h8, h97, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
        · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
          · linarith only [h101, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
            · rcases m.htr 1 3 5 (by decide) (by decide) with h104 | h104
              · linarith only [h1, h104, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                · linarith only [h0, h100, h104, h106, h4, h6, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h109 | h109
                    · linarith only [h0, h100, h104, h109, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h100, h108, h109, h4, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h100, h108, h4, h5, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h100, h103, h7, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
          · linarith only [h114, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h116 | h116
            · rcases m.htr 1 3 5 (by decide) (by decide) with h117 | h117
              · linarith only [h0, h117, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                · linarith only [h0, h116, h117, h119, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                    · linarith only [h0, h116, h117, h122, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                      · linarith only [h0, h119, h121, h122, h124, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h100, h116, h124, h126, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
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
                            linarith only [h0, h100, h121, h122, h4, h6, hlam, p128_2]
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
                            linarith only [h7, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h100, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h114, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h1, hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h122, h4, h6, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [hlam, p128_0]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h122, h4, h6, h7, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p128_1]
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
                            linarith only [h0, h116, h122, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1]
                          · have p128_0 := h128c.1
                            have p128_1 := h128c.2.1
                            have p128_2 := h128c.2.2.1
                            have p128_3 := h128c.2.2.2
                            linarith only [h116, hlam, p128_0]
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
                                · linarith only [h169, h7, hlam]
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
                  · linarith only [h1, h116, h121, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
              · linarith only [h1, h183, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                · linarith only [h0, h116, h185, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                    · linarith only [h0, h183, h188, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · linarith only [h116, h187, h188, hc13, hc35, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h191 | h191
                    · linarith only [h187, h191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
                      · linarith only [h0, h187, h193, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h195 | h195
                        · linarith only [h0, h195, h4, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · linarith only [h187, h195, h7, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
      · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
        · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
          · linarith only [h0, h200, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
            · rcases m.htr 1 3 5 (by decide) (by decide) with h203 | h203
              · linarith only [h1, h203, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                · linarith only [h2, h205, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                    · linarith only [h198, h200, h208, h3, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
                      · linarith only [h199, h200, h205, h210, hlam]
                      · linarith only [h198, h200, h207, h210, hc34, hc45, hlam, hphi]
                  · linarith only [h207, h5, h6, hc23, hc35, hlam, hphi]
            · linarith only [h202, h5, h6, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
          · linarith only [h199, h215, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
            · linarith only [h198, h199, h217, hlam]
            · linarith only [h217, h5, h6, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
        · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
          · linarith only [h198, h221, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
            · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
              · linarith only [h198, h220, h224, h4, h6, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                · linarith only [h198, h220, h226, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                    · linarith only [h229, h4, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                      · linarith only [h198, h220, h224, h226, h231, h4, h6, hc13, hc35, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                        · linarith only [h198, h220, h228, h229, h231, h233, hlam]
                        · linarith only [h198, h220, h228, h233, h4, h6, hc34, hc45, hlam, hphi]
                  · linarith only [h198, h220, h228, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h198, h220, h223, h5, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
          · linarith only [h198, h238, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h240 | h240
            · rcases m.htr 1 3 5 (by decide) (by decide) with h241 | h241
              · linarith only [h1, h198, h241, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                · linarith only [h2, h243, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                    · linarith only [h246, h4, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h245, h248, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                        · linarith only [h220, h240, h248, h250, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h254 | h254
                            · rcases p252_3 (m.d 1 2) (by simp) with h255 | h255
                              · linarith only [h255, hlam, p252_0]
                              · rcases p252_3 (m.d 1 3) (by simp) with h257 | h257
                                · linarith only [h1, h257, hlam]
                                · linarith only [h198, h257, hlam]
                            · linarith only [h254, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h261 | h261
                            · rcases p252_3 (m.d 1 2) (by simp) with h262 | h262
                              · linarith only [h0, h262, hlam]
                              · rcases p252_3 (m.d 1 3) (by simp) with h264 | h264
                                · linarith only [h264, hlam, p252_0]
                                · rcases p252_3 (m.d 1 4) (by simp) with h266 | h266
                                  · linarith only [h2, h266, hlam]
                                  · rcases p252_3 (m.d 1 5) (by simp) with h268 | h268
                                    · linarith only [h268, h3, hlam]
                                    · linarith only [h241, h268, hlam]
                            · linarith only [h261, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h272 | h272
                            · rcases p252_3 (m.d 1 2) (by simp) with h273 | h273
                              · linarith only [h0, h273, hlam]
                              · rcases p252_3 (m.d 1 3) (by simp) with h275 | h275
                                · linarith only [h1, h275, hlam]
                                · linarith only [h240, h275, hlam]
                            · linarith only [h272, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p252_1, u5ehi1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h0, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h198, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h220, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h238, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h1, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h1, h250, h6, hc12, hc45, hlam, hphi, ht23, ht34, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h1, h250, h6, hc14, hc45, hlam, hphi, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h241, hlam, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h2, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h2, h250, h5, h6, hc12, hc45, hlam, hphi, ht23, ht34, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h240, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h243, hlam, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h3, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h296 | h296
                            · rcases p252_3 (m.d 1 2) (by simp) with h297 | h297
                              · linarith only [h238, h297, hlam]
                              · rcases p252_3 (m.d 1 3) (by simp) with h299 | h299
                                · linarith only [h241, h299, hlam]
                                · linarith only [h198, h299, hlam]
                            · linarith only [h0, h296, hlam]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h240, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h304 | h304
                            · rcases p252_3 (m.d 1 2) (by simp) with h305 | h305
                              · linarith only [h238, h305, hlam]
                              · rcases p252_3 (m.d 1 3) (by simp) with h307 | h307
                                · linarith only [h241, h307, hlam]
                                · linarith only [h240, h307, hlam]
                            · linarith only [h2, h304, hlam]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                  · linarith only [h1, h240, h245, h6, hc23, hc35, hlam, hphi]
            · linarith only [h240, h5, h6, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
    · linarith only [h314, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h316 | h316
      · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
        · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
          · linarith only [h0, h318, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
            · linarith only [h1, h320, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
              · linarith only [h1, h3, h314, h322, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                · linarith only [h0, h317, h324, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                  · linarith only [h3, h316, h318, h326, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                    · linarith only [h1, h3, h314, h316, h328, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                      · linarith only [h317, h318, h324, h328, h330, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                        · linarith only [h317, h318, h326, h330, h332, hc23, hc34, hlam, hphi]
                        · rcases h1bigk with h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 1) (by simp) with h336 | h336
                            · rcases p334_3 (m.d 1 2) (by simp) with h337 | h337
                              · linarith only [h337, hlam, p334_0]
                              · rcases p334_3 (m.d 1 3) (by simp) with h339 | h339
                                · linarith only [h1, h339, hlam]
                                · rcases p334_3 (m.d 1 4) (by simp) with h341 | h341
                                  · linarith only [h2, h341, hlam]
                                  · rcases p334_3 (m.d 1 5) (by simp) with h343 | h343
                                    · linarith only [h3, h343, hlam]
                                    · linarith only [h318, h343, hlam]
                            · linarith only [h336, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 1) (by simp) with h347 | h347
                            · rcases p334_3 (m.d 1 2) (by simp) with h348 | h348
                              · linarith only [h0, h348, hlam]
                              · linarith only [h316, h348, hlam]
                            · linarith only [h347, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 1) (by simp) with h352 | h352
                            · rcases p334_3 (m.d 1 2) (by simp) with h353 | h353
                              · linarith only [h0, h353, hlam]
                              · linarith only [h317, h353, hlam]
                            · linarith only [h352, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p334_1, u5ehi1]
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
                            linarith only [h316, h318, h328, hc23, hc35, hlam, hphi, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h317, h318, h326, h328, hc23, hc35, hlam, hphi, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h318, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h1, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h316, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h320, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h322, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h2, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h317, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h2, h316, h332, h5, hc23, hc45, hlam, hphi, ht34, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h324, hlam, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h3, hlam, p334_0]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [h3, h316, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p334_1]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 1) (by simp) with h375 | h375
                            · rcases p334_3 (m.d 1 2) (by simp) with h376 | h376
                              · linarith only [h318, h376, hlam]
                              · linarith only [h316, h376, hlam]
                            · linarith only [h1, h375, hlam]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            rcases p334_3 (m.d 0 1) (by simp) with h380 | h380
                            · rcases p334_3 (m.d 1 2) (by simp) with h381 | h381
                              · linarith only [h318, h381, hlam]
                              · linarith only [h317, h381, hlam]
                            · linarith only [h2, h380, hlam]
                          · have p334_0 := h334c.1
                            have p334_1 := h334c.2.1
                            have p334_2 := h334c.2.2.1
                            have p334_3 := h334c.2.2.2
                            linarith only [hlam, p334_0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h386 | h386
          · linarith only [h317, h386, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
            · linarith only [h1, h388, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
              · linarith only [h1, h3, h314, h390, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                · linarith only [h2, h392, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                  · linarith only [h394, h4, h5, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                    · linarith only [h314, h316, h396, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                      · linarith only [h316, h317, h392, h394, h398, hc23, hc34, hlam, hphi]
                      · linarith only [h316, h317, h398, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
        · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
          · linarith only [h316, h4, h402, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h404 | h404
            · linarith only [h316, h4, h401, h404, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h316, h401, h404, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
          · linarith only [h401, h407, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
            · linarith only [h316, h4, h409, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
              · linarith only [h314, h316, h4, h411, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h413 | h413
                · linarith only [h2, h413, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                  · linarith only [h4, h415, h5, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                    · linarith only [h314, h4, h417, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h420 | h420
                        · rcases h1bigk with h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            rcases p421_3 (m.d 0 1) (by simp) with h423 | h423
                            · rcases p421_3 (m.d 1 2) (by simp) with h424 | h424
                              · linarith only [h424, hlam, p421_0]
                              · rcases p421_3 (m.d 1 3) (by simp) with h426 | h426
                                · linarith only [h1, h426, hlam]
                                · linarith only [h316, h426, hlam]
                            · linarith only [h423, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            rcases p421_3 (m.d 0 1) (by simp) with h430 | h430
                            · rcases p421_3 (m.d 1 2) (by simp) with h431 | h431
                              · linarith only [h0, h431, hlam]
                              · rcases p421_3 (m.d 1 3) (by simp) with h433 | h433
                                · linarith only [h433, hlam, p421_0]
                                · rcases p421_3 (m.d 1 4) (by simp) with h435 | h435
                                  · linarith only [h2, h435, hlam]
                                  · linarith only [h409, h435, hlam]
                            · linarith only [h430, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            rcases p421_3 (m.d 0 1) (by simp) with h439 | h439
                            · rcases p421_3 (m.d 1 2) (by simp) with h440 | h440
                              · linarith only [h0, h440, hlam]
                              · rcases p421_3 (m.d 1 3) (by simp) with h442 | h442
                                · linarith only [h1, h442, hlam]
                                · rcases p421_3 (m.d 1 4) (by simp) with h444 | h444
                                  · linarith only [h444, hlam, p421_0]
                                  · rcases p421_3 (m.d 1 5) (by simp) with h446 | h446
                                    · linarith only [h3, h446, hlam]
                                    · linarith only [h413, h446, hlam]
                            · linarith only [h439, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht5b, p421_1, u5ehi1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h0, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h316, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h401, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h407, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h1, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h409, h413, h415, h419, hc12, hc34, hlam, hphi, ht23, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h409, hlam, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h411, hlam, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h2, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h413, h415, h419, hc12, hc34, hlam, hphi, ht23, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h413, h415, h419, hc13, hc34, hlam, hphi, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h413, hlam, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h3, hlam, p421_0]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h413, h415, h419, hc12, hc34, hlam, hphi, ht23, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h316, h413, h415, h419, hc12, hc34, hlam, hphi, ht23, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [h401, h413, h415, h419, hc12, hc34, hlam, hphi, ht23, p421_1]
                          · have p421_0 := h421c.1
                            have p421_1 := h421c.2.1
                            have p421_2 := h421c.2.2.1
                            have p421_3 := h421c.2.2.2
                            linarith only [hlam, p421_0]
                        · linarith only [h415, h419, h420, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h316, h415, h419, h472, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h316, h4, h472, h5, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
