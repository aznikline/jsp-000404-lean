import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
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
                                linarith only [h9, hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [hlam, p35_0]
                              · have p35_0 := h35c.1
                                have p35_1 := h35c.2.1
                                have p35_2 := h35c.2.2.1
                                have p35_3 := h35c.2.2.2
                                linarith only [h12, hlam, p35_0]
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
                                linarith only [h10, hlam, p35_0]
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
                                linarith only [h11, hlam, p35_0]
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
                        · linarith only [h104, h109, h110, h9, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h104, h109, h4, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h108, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h107, hc13, hlam, hphi, ht34, ht45, u5elo3]
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
                                linarith only [h9, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h104, hlam, p128_1]
                              · have p128_0 := h128c.1
                                have p128_1 := h128c.2.1
                                have p128_2 := h128c.2.2.1
                                have p128_3 := h128c.2.2.2
                                linarith only [h0, h104, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p128_1]
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
                                linarith only [h121, hlam, p128_1]
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
                                linarith only [h120, hlam, p128_0]
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
                          · linarith only [h104, h123, h126, hc14, hlam, hphi, ht45, u5elo1]
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
        · linarith only [h8, hc04, hlam, hphi, ht45, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h193 | h193
        · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
          · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
            · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
              · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                · linarith only [h1, h197, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                      · linarith only [h0, h194, h201, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
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
                                linarith only [h194, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h197, hlam, p206_0]
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
                                        · rcases h2bigk with h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c | h245c
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h194, h196, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p206_1, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 2) (by simp) with h248 | h248
                                            · rcases p245_3 (m.d 1 2) (by simp) with h249 | h249
                                              · linarith only [h0, h249, hlam]
                                              · linarith only [h194, h249, hlam]
                                            · linarith only [h248, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 2) (by simp) with h253 | h253
                                            · rcases p245_3 (m.d 1 2) (by simp) with h254 | h254
                                              · linarith only [h0, h254, hlam]
                                              · linarith only [h195, h254, hlam]
                                            · linarith only [h253, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 2) (by simp) with h258 | h258
                                            · rcases p245_3 (m.d 1 2) (by simp) with h259 | h259
                                              · linarith only [h0, h259, hlam]
                                              · linarith only [h196, h259, hlam]
                                            · linarith only [h258, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, hlam, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h201, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            rcases p245_3 (m.d 0 2) (by simp) with h267 | h267
                                            · rcases p245_3 (m.d 1 2) (by simp) with h268 | h268
                                              · rcases p245_3 (m.d 2 3) (by simp) with h269 | h269
                                                · linarith only [h194, h269, hlam]
                                                · linarith only [h203, h269, hlam]
                                              · linarith only [h268, hlam, p245_0]
                                            · linarith only [h267, h6, hlam]
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
                                            linarith only [h201, hlam, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h194, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h5, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h195, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h1, h195, h196, h203, h205, h7, hc01, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p206_1, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h0, h195, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p245_1]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h6, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h196, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h203, hlam, p245_0]
                                          · have p245_0 := h245c.1
                                            have p245_1 := h245c.2.1
                                            have p245_2 := h245c.2.2.1
                                            have p245_3 := h245c.2.2.2
                                            linarith only [h204, hlam, p245_1]
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
                                linarith only [h195, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h194, h2, h203, h205, hc01, hc45, hlam, hphi, ht0b, ht5b, p206_1]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                rcases p206_3 (m.d 0 1) (by simp) with h297 | h297
                                · rcases p206_3 (m.d 1 2) (by simp) with h298 | h298
                                  · rcases p206_3 (m.d 1 3) (by simp) with h299 | h299
                                    · linarith only [h197, h299, hlam]
                                    · linarith only [h199, h299, hlam]
                                  · linarith only [h196, h298, hlam]
                                · linarith only [h297, h3, hlam]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h3, hlam, p206_0]
                              · have p206_0 := h206c.1
                                have p206_1 := h206c.2.1
                                have p206_2 := h206c.2.2.1
                                have p206_3 := h206c.2.2.2
                                linarith only [h196, hlam, p206_0]
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
                          · linarith only [h200, h201, h204, hc23, hlam, hphi, ht34, ht45, u5elo1]
                        · linarith only [h1, h199, h203, h7, hc23, hc34, hlam, hphi]
                    · linarith only [h197, h200, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h194, h199, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h196, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h315 | h315
              · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
                · linarith only [h1, h194, h195, h316, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                      · linarith only [h194, h195, h320, h5, h7, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                        · linarith only [h0, h194, h195, h322, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h322, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h319, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h318, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h315, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
            · rcases m.htr 1 2 5 (by decide) (by decide) with h329 | h329
              · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                · linarith only [h194, h328, h330, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h194, h328, h330, hlam]
              · linarith only [h328, h329, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
              · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                · linarith only [h1, h335, h7, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                      · linarith only [h339, h4, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h342 | h342
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                            · rcases h1bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h346 | h346
                                · rcases p344_3 (m.d 1 2) (by simp) with h347 | h347
                                  · linarith only [h347, hlam, p344_0]
                                  · rcases p344_3 (m.d 1 3) (by simp) with h349 | h349
                                    · linarith only [h1, h349, hlam]
                                    · linarith only [h194, h349, hlam]
                                · linarith only [h346, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h353 | h353
                                · rcases p344_3 (m.d 1 2) (by simp) with h354 | h354
                                  · linarith only [h0, h354, hlam]
                                  · rcases p344_3 (m.d 1 3) (by simp) with h356 | h356
                                    · linarith only [h356, hlam, p344_0]
                                    · rcases p344_3 (m.d 1 4) (by simp) with h358 | h358
                                      · linarith only [h2, h358, hlam]
                                      · linarith only [h335, h358, hlam]
                                · linarith only [h353, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h362 | h362
                                · rcases p344_3 (m.d 1 2) (by simp) with h363 | h363
                                  · linarith only [h0, h363, hlam]
                                  · rcases p344_3 (m.d 1 3) (by simp) with h365 | h365
                                    · linarith only [h1, h365, hlam]
                                    · rcases p344_3 (m.d 1 4) (by simp) with h367 | h367
                                      · linarith only [h367, hlam, p344_0]
                                      · rcases p344_3 (m.d 1 5) (by simp) with h369 | h369
                                        · linarith only [h3, h369, hlam]
                                        · rcases h2bigk with h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            rcases p371_3 (m.d 0 2) (by simp) with h373 | h373
                                            · rcases p371_3 (m.d 1 2) (by simp) with h374 | h374
                                              · linarith only [h0, h374, hlam]
                                              · rcases p371_3 (m.d 2 3) (by simp) with h376 | h376
                                                · linarith only [h376, h4, hlam]
                                                · linarith only [h194, h376, hlam]
                                            · linarith only [h0, h373, hlam]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h0, h194, h334, h341, h343, hc01, hc45, hlam, hphi, ht0b, ht5b, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h0, h194, h334, h339, h341, h343, hc01, hc45, hlam, hphi, ht0b, ht5b, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h194, h334, h4, hlam, p371_2]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h0, hlam, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h194, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h328, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h194, h341, h343, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h4, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h339, hlam, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            rcases p371_3 (m.d 0 2) (by simp) with h392 | h392
                                            · rcases p371_3 (m.d 1 2) (by simp) with h393 | h393
                                              · linarith only [h194, h393, hlam]
                                              · linarith only [h334, h393, hlam]
                                            · linarith only [h392, h6, hlam]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h5, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h334, h341, h343, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h0, h194, h334, h341, h343, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            rcases p371_3 (m.d 0 2) (by simp) with h401 | h401
                                            · rcases p371_3 (m.d 1 2) (by simp) with h402 | h402
                                              · linarith only [h328, h402, hlam]
                                              · linarith only [h334, h402, hlam]
                                            · linarith only [h401, h6, hlam]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h6, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h334, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h341, hlam, p371_0]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [h342, hlam, p371_1]
                                          · have p371_0 := h371c.1
                                            have p371_1 := h371c.2.1
                                            have p371_2 := h371c.2.2.1
                                            have p371_3 := h371c.2.2.2
                                            linarith only [hlam, p371_0]
                                · linarith only [h362, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h412 | h412
                                · rcases p344_3 (m.d 1 2) (by simp) with h413 | h413
                                  · linarith only [h0, h413, hlam]
                                  · linarith only [h334, h413, hlam]
                                · linarith only [h412, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h0, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h194, hlam, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h328, hlam, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h0, h194, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h1, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h335, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h426 | h426
                                · rcases p344_3 (m.d 1 2) (by simp) with h427 | h427
                                  · linarith only [h194, h427, hlam]
                                  · linarith only [h334, h427, hlam]
                                · linarith only [h3, h426, hlam]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h2, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h2, h334, h341, h343, hc01, hc45, hlam, hphi, ht0b, ht5b, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h0, h194, h328, h334, h341, h343, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h435 | h435
                                · rcases p344_3 (m.d 1 2) (by simp) with h436 | h436
                                  · linarith only [h328, h436, hlam]
                                  · linarith only [h334, h436, hlam]
                                · linarith only [h3, h435, hlam]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h3, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h334, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h337, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h338, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                            · linarith only [h194, h334, h341, h343, h4, h7, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h328, h342, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h194, h334, h341, hc25, hlam, hphi, u5elo3]
                    · linarith only [h194, h334, h335, h338, hc25, hlam, hphi, u5elo4]
                  · linarith only [h194, h334, h337, hc25, hlam, hphi, u5elo3]
              · linarith only [h334, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h193, h7, hc03, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h453 | h453
    · rcases m.htr 0 3 4 (by decide) (by decide) with h454 | h454
      · linarith only [h4, h454, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
        · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
          · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
            · linarith only [h0, h458, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
              · rcases m.htr 1 3 4 (by decide) (by decide) with h461 | h461
                · linarith only [h1, h454, h461, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h463 | h463
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                      · linarith only [h0, h1, h454, h457, h463, h465, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h467 | h467
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                            · rcases h1bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h457, h467, h469, hc01, hc45, hlam, hphi, ht0b, ht5b, p470_1]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                rcases p470_3 (m.d 0 1) (by simp) with h473 | h473
                                · rcases p470_3 (m.d 1 2) (by simp) with h474 | h474
                                  · linarith only [h0, h474, hlam]
                                  · linarith only [h457, h474, hlam]
                                · linarith only [h473, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h457, h458, h467, h469, hc01, hc45, hlam, hphi, ht0b, ht5b, p470_1]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                rcases p470_3 (m.d 0 1) (by simp) with h479 | h479
                                · rcases p470_3 (m.d 1 2) (by simp) with h480 | h480
                                  · linarith only [h0, h480, hlam]
                                  · linarith only [h460, h480, hlam]
                                · linarith only [h479, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h0, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h0, h457, h467, h469, hc01, hc45, hlam, hphi, ht0b, ht5b, p470_1]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h458, hlam, p470_1]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                rcases p470_3 (m.d 0 1) (by simp) with h488 | h488
                                · rcases p470_3 (m.d 1 2) (by simp) with h489 | h489
                                  · rcases p470_3 (m.d 1 3) (by simp) with h490 | h490
                                    · linarith only [h457, h490, hlam]
                                    · linarith only [h463, h490, hlam]
                                  · linarith only [h460, h489, hlam]
                                · linarith only [h3, h488, hlam]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h1, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h457, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h461, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                rcases p470_3 (m.d 0 1) (by simp) with h499 | h499
                                · rcases p470_3 (m.d 1 2) (by simp) with h500 | h500
                                  · rcases p470_3 (m.d 1 3) (by simp) with h501 | h501
                                    · rcases p470_3 (m.d 1 4) (by simp) with h502 | h502
                                      · rcases p470_3 (m.d 1 5) (by simp) with h503 | h503
                                        · linarith only [h463, h503, hlam]
                                        · rcases h2bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h465, h5, hc12, hc34, hlam, hphi, ht23, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h465, h467, h469, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h5, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            rcases p505_3 (m.d 0 2) (by simp) with h510 | h510
                                            · rcases p505_3 (m.d 1 2) (by simp) with h511 | h511
                                              · linarith only [h0, h511, hlam]
                                              · linarith only [h460, h511, hlam]
                                            · linarith only [h510, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h0, hlam, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h0, h467, h469, hc01, hc45, hlam, hphi, ht0b, ht5b, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h458, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            rcases p505_3 (m.d 0 2) (by simp) with h519 | h519
                                            · rcases p505_3 (m.d 1 2) (by simp) with h520 | h520
                                              · rcases p505_3 (m.d 2 3) (by simp) with h521 | h521
                                                · linarith only [h457, h521, hlam]
                                                · linarith only [h467, h521, hlam]
                                              · linarith only [h520, hlam, p505_0]
                                            · linarith only [h453, h519, hlam]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h4, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h457, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h465, hlam, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h4, h465, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h1, h4, h465, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p470_1, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h457, h465, hc23, hc34, hlam, hphi, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            rcases p505_3 (m.d 0 2) (by simp) with h533 | h533
                                            · linarith only [h5, h533, hlam]
                                            · linarith only [h4, h533, hlam]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h1, h4, h460, h5, hlam, p470_1, p505_2]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h453, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h460, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h467, hlam, p505_0]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [h468, hlam, p505_1]
                                          · have p505_0 := h505c.1
                                            have p505_1 := h505c.2.1
                                            have p505_2 := h505c.2.2.1
                                            have p505_3 := h505c.2.2.2
                                            linarith only [hlam, p505_0]
                                      · linarith only [h464, h502, hlam]
                                    · linarith only [h463, h501, hlam]
                                  · linarith only [h460, h500, hlam]
                                · linarith only [h3, h499, hlam]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h2, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h2, h457, h467, h469, hc01, hc45, hlam, hphi, ht0b, ht5b, p470_1]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h2, h457, h467, h469, hc01, hc45, hlam, hphi, ht0b, ht5b, p470_1]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                rcases p470_3 (m.d 0 1) (by simp) with h551 | h551
                                · rcases p470_3 (m.d 1 2) (by simp) with h552 | h552
                                  · linarith only [h458, h552, hlam]
                                  · linarith only [h460, h552, hlam]
                                · linarith only [h3, h551, hlam]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h3, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h460, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h463, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [h464, hlam, p470_0]
                              · have p470_0 := h470c.1
                                have p470_1 := h470c.2.1
                                have p470_2 := h470c.2.2.1
                                have p470_3 := h470c.2.2.2
                                linarith only [hlam, p470_0]
                            · linarith only [h469, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h3, h464, h468, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h467, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h464, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h463, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h457, h460, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h4, h457, h5, hc12, hc24, hlam, hphi]
        · linarith only [h456, hc04, hlam, hphi, ht45, u5elo4]
    · linarith only [h453, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

end R2N4
