import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                            · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h18, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h14, h17, h3, hc24, hlam, hphi, ht45, u5elo0]
                        · linarith only [h16, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h12, h15, h23, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h23, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h14, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h13, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h12, h28, h30, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                            · rcases h1bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h32, h34, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                rcases p35_3 (m.d 0 1) (by simp) with h38 | h38
                                · rcases p35_3 (m.d 1 2) (by simp) with h39 | h39
                                  · linarith only [h0, h39, hlam]
                                  · linarith only [h39, h9, hlam]
                                · linarith only [h38, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                rcases p35_3 (m.d 0 1) (by simp) with h43 | h43
                                · rcases p35_3 (m.d 1 2) (by simp) with h44 | h44
                                  · linarith only [h0, h44, hlam]
                                  · linarith only [h10, h44, hlam]
                                · linarith only [h43, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                rcases p35_3 (m.d 0 1) (by simp) with h48 | h48
                                · rcases p35_3 (m.d 1 2) (by simp) with h49 | h49
                                  · linarith only [h0, h49, hlam]
                                  · linarith only [h11, h49, hlam]
                                · linarith only [h48, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h0, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h0, h32, h34, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h0, h12, h32, h34, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                rcases p35_3 (m.d 0 1) (by simp) with h57 | h57
                                · rcases p35_3 (m.d 1 2) (by simp) with h58 | h58
                                  · rcases p35_3 (m.d 1 3) (by simp) with h59 | h59
                                    · linarith only [h59, h9, hlam]
                                    · linarith only [h28, h59, hlam]
                                  · linarith only [h11, h58, hlam]
                                · linarith only [h3, h57, hlam]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h1, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h9, hlam, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h12, hlam, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h0, h11, h12, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h2, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h10, hlam, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h2, h32, h34, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                rcases p35_3 (m.d 0 1) (by simp) with h73 | h73
                                · rcases p35_3 (m.d 1 2) (by simp) with h74 | h74
                                  · rcases p35_3 (m.d 1 3) (by simp) with h75 | h75
                                    · linarith only [h12, h75, hlam]
                                    · linarith only [h28, h75, hlam]
                                  · linarith only [h11, h74, hlam]
                                · linarith only [h3, h73, hlam]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h3, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h11, hlam, p35_1]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h28, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h29, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [hlam, p35_0]
                            · linarith only [h12, h34, hc14, hlam, hphi, ht45, u5elo4]
                          · linarith only [h33, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h32, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h12, h29, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h28, h9, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h11, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
              · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                · linarith only [h10, h9, h92, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h10, h9, h92, h96, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h10, h4, h7, h9, h96, h98, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h98, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h10, h95, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h94, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h9, h91, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
            · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
              · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h0, h104, h111, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h111, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h110, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h105, h109, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h108, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h104, h107, h9, hc24, hlam, hphi, ht45, u5elo3]
                · linarith only [h104, h106, h9, hlam]
              · linarith only [h104, h105, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
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
                                rcases p128_3 (m.d 0 1) (by simp) with h130 | h130
                                · rcases p128_3 (m.d 1 2) (by simp) with h131 | h131
                                  · linarith only [h131, hlam, p128_0]
                                  · rcases p128_3 (m.d 1 3) (by simp) with h133 | h133
                                    · linarith only [h1, h133, hlam]
                                    · linarith only [h133, h9, hlam]
                                · linarith only [h130, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h121, h127, hc01, hc45, hlam, hphi, ht0b, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h138 | h138
                                · rcases p128_3 (m.d 1 2) (by simp) with h139 | h139
                                  · linarith only [h0, h139, hlam]
                                  · rcases p128_3 (m.d 1 3) (by simp) with h141 | h141
                                    · linarith only [h1, h141, hlam]
                                    · linarith only [h121, h141, hlam]
                                · linarith only [h138, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h145 | h145
                                · rcases p128_3 (m.d 1 2) (by simp) with h146 | h146
                                  · linarith only [h0, h146, hlam]
                                  · linarith only [h120, h146, hlam]
                                · linarith only [h145, hlam, p128_0]
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
                                linarith only [h9, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h104, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h104, h124, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h1, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h120, h125, h127, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h104, h120, h125, h127, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                rcases p128_3 (m.d 0 1) (by simp) with h159 | h159
                                · rcases p128_3 (m.d 1 2) (by simp) with h160 | h160
                                  · linarith only [h160, h9, hlam]
                                  · linarith only [h120, h160, hlam]
                                · linarith only [h159, h3, hlam]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h2, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h120, h125, h127, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p128_1]
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
                                rcases p128_3 (m.d 0 1) (by simp) with h168 | h168
                                · rcases p128_3 (m.d 1 2) (by simp) with h169 | h169
                                  · linarith only [h104, h169, hlam]
                                  · linarith only [h120, h169, hlam]
                                · linarith only [h168, h3, hlam]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h3, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h120, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h122, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h123, hlam, p128_0]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [hlam, p128_0]
                            · linarith only [h127, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h104, h123, h126, h3, hc14, hlam, hphi, ht45, u5elo0]
                        · linarith only [h125, h9, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h0, h120, h124, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h104, h120, h123, hc25, hlam, hphi, u5elo4]
                  · linarith only [h122, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                      · linarith only [h0, h120, h121, h186, h4, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h120, h186, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h120, h121, h185, h9, hc25, hlam, hphi, u5elo4]
                  · linarith only [h120, h184, h9, hc25, hlam, hphi, u5elo3]
              · linarith only [h120, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
        · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
          · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
            · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
              · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                · linarith only [h1, h197, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                      · linarith only [h1, h194, h199, h201, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h205 | h205
                            · rcases h1bigk with h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h194, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h209 | h209
                                · rcases p206_3 (m.d 1 2) (by simp) with h210 | h210
                                  · linarith only [h0, h210, hlam]
                                  · linarith only [h194, h210, hlam]
                                · linarith only [h209, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h214 | h214
                                · rcases p206_3 (m.d 1 2) (by simp) with h215 | h215
                                  · linarith only [h0, h215, hlam]
                                  · linarith only [h195, h215, hlam]
                                · linarith only [h214, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h219 | h219
                                · rcases p206_3 (m.d 1 2) (by simp) with h220 | h220
                                  · linarith only [h0, h220, hlam]
                                  · linarith only [h196, h220, hlam]
                                · linarith only [h219, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h0, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h0, h194, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h0, h194, h197, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h228 | h228
                                · rcases p206_3 (m.d 1 2) (by simp) with h229 | h229
                                  · rcases p206_3 (m.d 1 3) (by simp) with h230 | h230
                                    · linarith only [h194, h230, hlam]
                                    · linarith only [h199, h230, hlam]
                                  · linarith only [h196, h229, hlam]
                                · linarith only [h228, h3, hlam]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h1, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h194, hlam, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h197, hlam, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h239 | h239
                                · rcases p206_3 (m.d 1 2) (by simp) with h240 | h240
                                  · rcases p206_3 (m.d 1 3) (by simp) with h241 | h241
                                    · rcases p206_3 (m.d 1 4) (by simp) with h242 | h242
                                      · rcases p206_3 (m.d 1 5) (by simp) with h243 | h243
                                        · linarith only [h199, h243, hlam]
                                        · rcases h3bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h196, h203, h205, hc03, hc45, hlam, hphi, ht0b, ht5b, p206_1, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h7, hc23, hc34, hlam, hphi, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h7, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 3) (by simp) with h250 | h250
                                            · rcases p245_3 (m.d 1 3) (by simp) with h251 | h251
                                              · linarith only [h1, h251, hlam]
                                              · linarith only [h199, h251, hlam]
                                            · linarith only [h250, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h1, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h1, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h197, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 3) (by simp) with h259 | h259
                                            · rcases p245_3 (m.d 1 3) (by simp) with h260 | h260
                                              · rcases p245_3 (m.d 2 3) (by simp) with h261 | h261
                                                · linarith only [h194, h261, hlam]
                                                · linarith only [h203, h261, hlam]
                                              · linarith only [h260, hlam, p245_0]
                                            · linarith only [h193, h259, hlam]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h4, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h194, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h201, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h194, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h1, h196, h203, h205, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p206_1, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h196, h203, h205, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p206_1, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 3) (by simp) with h273 | h273
                                            · linarith only [h273, h7, hlam]
                                            · linarith only [h273, h4, hlam]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h1, h196, h203, h7, hlam, p206_1, p245_2]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h193, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h199, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h203, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h205, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                      · linarith only [h200, h242, hlam]
                                    · linarith only [h199, h241, hlam]
                                  · linarith only [h196, h240, hlam]
                                · linarith only [h239, h3, hlam]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h2, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h195, hlam, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h0, h195, h199, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h291 | h291
                                · rcases p206_3 (m.d 1 2) (by simp) with h292 | h292
                                  · rcases p206_3 (m.d 1 3) (by simp) with h293 | h293
                                    · linarith only [h197, h293, hlam]
                                    · linarith only [h199, h293, hlam]
                                  · linarith only [h196, h292, hlam]
                                · linarith only [h291, h3, hlam]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h3, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h196, hlam, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h199, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h200, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                            · linarith only [h205, h7, hc04, hlam, hphi, ht45, u5elo4]
                          · linarith only [h200, h201, h203, h204, hc35, hlam, hphi, u5elo1]
                        · linarith only [h203, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h197, h200, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h194, h199, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h196, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
              · rcases m.htr 1 3 4 (by decide) (by decide) with h310 | h310
                · linarith only [h1, h310, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
                      · linarith only [h194, h195, h314, h5, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                        · linarith only [h0, h194, h195, h316, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h316, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h195, h313, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h312, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h194, h309, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h322 | h322
            · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
              · rcases m.htr 1 3 4 (by decide) (by decide) with h324 | h324
                · linarith only [h194, h324, h4, h7, hlam]
                · linarith only [h194, h322, h324, hlam]
              · linarith only [h323, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h328 | h328
              · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                · linarith only [h1, h329, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                      · linarith only [h333, h4, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h335 | h335
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h336 | h336
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                            · rcases h1bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                rcases p338_3 (m.d 0 1) (by simp) with h340 | h340
                                · rcases p338_3 (m.d 1 2) (by simp) with h341 | h341
                                  · linarith only [h341, hlam, p338_0]
                                  · rcases p338_3 (m.d 1 3) (by simp) with h343 | h343
                                    · linarith only [h1, h343, hlam]
                                    · linarith only [h194, h343, hlam]
                                · linarith only [h340, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                rcases p338_3 (m.d 0 1) (by simp) with h347 | h347
                                · rcases p338_3 (m.d 1 2) (by simp) with h348 | h348
                                  · linarith only [h0, h348, hlam]
                                  · rcases p338_3 (m.d 1 3) (by simp) with h350 | h350
                                    · linarith only [h350, hlam, p338_0]
                                    · rcases p338_3 (m.d 1 4) (by simp) with h352 | h352
                                      · linarith only [h2, h352, hlam]
                                      · linarith only [h329, h352, hlam]
                                · linarith only [h347, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                rcases p338_3 (m.d 0 1) (by simp) with h356 | h356
                                · rcases p338_3 (m.d 1 2) (by simp) with h357 | h357
                                  · linarith only [h0, h357, hlam]
                                  · rcases p338_3 (m.d 1 3) (by simp) with h359 | h359
                                    · linarith only [h1, h359, hlam]
                                    · rcases p338_3 (m.d 1 4) (by simp) with h361 | h361
                                      · linarith only [h361, hlam, p338_0]
                                      · rcases p338_3 (m.d 1 5) (by simp) with h363 | h363
                                        · linarith only [h3, h363, hlam]
                                        · rcases h3bigk with h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h7, hc13, hc34, hlam, hphi, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h194, h328, h335, h337, hc03, hc45, hlam, hphi, ht0b, ht5b, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h7, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 3) (by simp) with h370 | h370
                                            · rcases p365_3 (m.d 1 3) (by simp) with h371 | h371
                                              · linarith only [h1, h371, hlam]
                                              · linarith only [h331, h371, hlam]
                                            · linarith only [h370, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h1, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h194, hlam, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h329, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h329, h337, hc01, hc45, hlam, hphi, ht0b, ht5b, p338_1, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h4, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h4, h7, hc13, hc34, hlam, hphi, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h333, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 3) (by simp) with h384 | h384
                                            · rcases p365_3 (m.d 1 3) (by simp) with h385 | h385
                                              · linarith only [h194, h385, hlam]
                                              · linarith only [h331, h385, hlam]
                                            · linarith only [h193, h384, hlam]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h194, h328, h335, h337, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            rcases p365_3 (m.d 0 3) (by simp) with h390 | h390
                                            · linarith only [h390, h7, hlam]
                                            · linarith only [h1, h390, hlam]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h194, h328, h335, h337, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p365_1]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h194, h328, h335, h4, h7, hlam, p365_2]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h193, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h331, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h335, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [h337, hlam, p365_0]
                                          · have p365_0 := h365c.1
                                            have p365_1 := h365c.2.1
                                            have p365_2 := h365c.2.2.1
                                            have p365_3 := h365c.2.2.2
                                            linarith only [hlam, p365_0]
                                · linarith only [h356, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                rcases p338_3 (m.d 0 1) (by simp) with h402 | h402
                                · rcases p338_3 (m.d 1 2) (by simp) with h403 | h403
                                  · linarith only [h0, h403, hlam]
                                  · linarith only [h328, h403, hlam]
                                · linarith only [h402, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h0, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h194, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h322, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h194, h4, h7, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p338_1]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h1, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h194, h4, h7, hc12, hc34, hlam, hphi, ht23, p338_1]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h329, hlam, p338_1]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                rcases p338_3 (m.d 0 1) (by simp) with h416 | h416
                                · rcases p338_3 (m.d 1 2) (by simp) with h417 | h417
                                  · linarith only [h194, h417, hlam]
                                  · linarith only [h328, h417, hlam]
                                · linarith only [h3, h416, hlam]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h2, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h2, h328, h335, h337, hc01, hc45, hlam, hphi, ht0b, ht5b, p338_1]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h194, h322, h328, h335, h337, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p338_1]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                rcases p338_3 (m.d 0 1) (by simp) with h425 | h425
                                · rcases p338_3 (m.d 1 2) (by simp) with h426 | h426
                                  · linarith only [h322, h426, hlam]
                                  · linarith only [h328, h426, hlam]
                                · linarith only [h3, h425, hlam]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h3, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h328, hlam, p338_1]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h331, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [h332, hlam, p338_0]
                              · have p338_0 := h338c.1
                                have p338_1 := h338c.2.1
                                have p338_2 := h338c.2.2.1
                                have p338_3 := h338c.2.2.2
                                linarith only [hlam, p338_0]
                            · linarith only [h337, h4, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h3, h322, h332, h336, hc14, hlam, hphi, ht45, u5elo0]
                        · linarith only [h194, h335, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h194, h328, h329, h332, hc25, hlam, hphi, u5elo4]
                  · linarith only [h194, h328, h331, hc25, hlam, hphi, u5elo3]
              · linarith only [h328, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h193, hc03, hlam, hphi, ht34, ht45, u5elo3]
    · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
    · rcases m.htr 0 3 4 (by decide) (by decide) with h444 | h444
      · linarith only [h4, h444, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h446 | h446
        · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
          · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
            · linarith only [h0, h448, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
              · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                · linarith only [h1, h444, h446, h451, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                      · linarith only [h0, h1, h444, h447, h453, h455, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h459 | h459
                            · rcases h1bigk with h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c | h460c
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h447, h457, h459, hc01, hc45, hlam, hphi, ht0b, ht5b, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                rcases p460_3 (m.d 0 1) (by simp) with h463 | h463
                                · rcases p460_3 (m.d 1 2) (by simp) with h464 | h464
                                  · linarith only [h0, h464, hlam]
                                  · linarith only [h447, h464, hlam]
                                · linarith only [h463, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h447, h448, h457, h459, hc01, hc45, hlam, hphi, ht0b, ht5b, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                rcases p460_3 (m.d 0 1) (by simp) with h469 | h469
                                · rcases p460_3 (m.d 1 2) (by simp) with h470 | h470
                                  · linarith only [h0, h470, hlam]
                                  · linarith only [h450, h470, hlam]
                                · linarith only [h469, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h0, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h0, h447, h457, h459, hc01, hc45, hlam, hphi, ht0b, ht5b, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h448, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                rcases p460_3 (m.d 0 1) (by simp) with h478 | h478
                                · rcases p460_3 (m.d 1 2) (by simp) with h479 | h479
                                  · rcases p460_3 (m.d 1 3) (by simp) with h480 | h480
                                    · linarith only [h447, h480, hlam]
                                    · linarith only [h453, h480, hlam]
                                  · linarith only [h450, h479, hlam]
                                · linarith only [h3, h478, hlam]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h1, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h447, hlam, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h451, hlam, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                rcases p460_3 (m.d 0 1) (by simp) with h489 | h489
                                · rcases p460_3 (m.d 1 2) (by simp) with h490 | h490
                                  · rcases p460_3 (m.d 1 3) (by simp) with h491 | h491
                                    · rcases p460_3 (m.d 1 4) (by simp) with h492 | h492
                                      · rcases p460_3 (m.d 1 5) (by simp) with h493 | h493
                                        · linarith only [h453, h493, hlam]
                                        · rcases h3bigk with h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h4, h455, h5, hc13, hc34, hlam, hphi, p495_1]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h4, h455, h457, h459, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p495_1]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h444, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            rcases p495_3 (m.d 0 3) (by simp) with h500 | h500
                                            · rcases p495_3 (m.d 1 3) (by simp) with h501 | h501
                                              · linarith only [h1, h501, hlam]
                                              · linarith only [h453, h501, hlam]
                                            · linarith only [h500, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h1, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h1, h457, h459, hc01, hc45, hlam, hphi, ht0b, ht5b, p495_1]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h451, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            rcases p495_3 (m.d 0 3) (by simp) with h509 | h509
                                            · rcases p495_3 (m.d 1 3) (by simp) with h510 | h510
                                              · rcases p495_3 (m.d 2 3) (by simp) with h511 | h511
                                                · linarith only [h447, h511, hlam]
                                                · linarith only [h457, h511, hlam]
                                              · linarith only [h510, hlam, p495_0]
                                            · linarith only [h446, h509, hlam]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h4, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h447, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h455, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h4, h455, h459, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p495_1]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h1, h450, h457, h459, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p460_1, p495_1]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h450, h457, h459, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p460_1, p495_1]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            rcases p495_3 (m.d 0 3) (by simp) with h523 | h523
                                            · linarith only [h444, h523, hlam]
                                            · linarith only [h4, h523, hlam]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h1, h4, h450, h455, h457, h5, hlam, p460_1, p495_2]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h446, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h453, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h457, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [h459, hlam, p495_0]
                                          · have p495_0 := h495c.1
                                            have p495_1 := h495c.2.1
                                            have p495_2 := h495c.2.2.1
                                            have p495_3 := h495c.2.2.2
                                            linarith only [hlam, p495_0]
                                      · linarith only [h454, h492, hlam]
                                    · linarith only [h453, h491, hlam]
                                  · linarith only [h450, h490, hlam]
                                · linarith only [h3, h489, hlam]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h2, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h2, h447, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h2, h453, h459, hc01, hc45, hlam, hphi, ht0b, ht5b, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                rcases p460_3 (m.d 0 1) (by simp) with h541 | h541
                                · rcases p460_3 (m.d 1 2) (by simp) with h542 | h542
                                  · linarith only [h448, h542, hlam]
                                  · linarith only [h450, h542, hlam]
                                · linarith only [h3, h541, hlam]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h3, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h450, hlam, p460_1]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h453, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [h454, hlam, p460_0]
                              · have p460_0 := h460c.1
                                have p460_1 := h460c.2.1
                                have p460_2 := h460c.2.2.1
                                have p460_3 := h460c.2.2.2
                                linarith only [hlam, p460_0]
                            · linarith only [h0, h447, h455, h457, h459, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h3, h447, h454, h457, h458, h5, hc35, hlam, hphi, u5elo0]
                        · linarith only [h457, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h454, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h453, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h447, h450, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h4, h447, h5, hc12, hc24, hlam, hphi]
        · linarith only [h446, hc03, hlam, hphi, ht34, ht45, u5elo3]
    · linarith only [h443, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

end R2N4
