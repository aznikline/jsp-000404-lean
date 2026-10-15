import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
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
                      · linarith only [h0, h15, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h18, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h12, h18, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h12, h13, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h12, h22, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h12, h25, h9, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h22, h27, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                            · rcases h1bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi2]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                rcases p31_3 (m.d 0 1) (by simp) with h34 | h34
                                · rcases p31_3 (m.d 1 2) (by simp) with h35 | h35
                                  · linarith only [h0, h35, hlam]
                                  · linarith only [h35, h9, hlam]
                                · linarith only [h34, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                rcases p31_3 (m.d 0 1) (by simp) with h39 | h39
                                · rcases p31_3 (m.d 1 2) (by simp) with h40 | h40
                                  · linarith only [h0, h40, hlam]
                                  · linarith only [h10, h40, hlam]
                                · linarith only [h39, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                rcases p31_3 (m.d 0 1) (by simp) with h44 | h44
                                · rcases p31_3 (m.d 1 2) (by simp) with h45 | h45
                                  · linarith only [h0, h45, hlam]
                                  · linarith only [h11, h45, hlam]
                                · linarith only [h44, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h0, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi1]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h0, h22, h24, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi2]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h0, h22, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi2]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h1, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h9, hlam, p31_1]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h12, hlam, p31_1]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h22, hlam, p31_1]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h2, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h10, hlam, p31_1]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h2, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi2]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h0, h12, h22, h4, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi2]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h3, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h11, hlam, p31_1]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h3, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p31_1, u3ehi2]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [h24, hlam, p31_0]
                              · have p31_0 := h31c.1
                                have p31_1 := h31c.2.1
                                have p31_2 := h31c.2.2.1
                                have p31_3 := h31c.2.2.2
                                linarith only [hlam, p31_0]
                            · linarith only [h0, h10, h12, h29, h30, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h2, h24, h25, h29, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h71, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h22, h73, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                          · linarith only [h10, h24, h75, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                            · linarith only [h0, h12, h24, h4, h6, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h0, h12, h4, h6, h77, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
              · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                · linarith only [h10, h82, h9, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                  · linarith only [h0, h4, h6, h82, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                      · linarith only [h0, h4, h82, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h10, h4, h6, h87, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h10, h86, h9, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h5, h81, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                      · linarith only [h0, h4, h9, h92, h97, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h9, h92, h94, h97, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                      · linarith only [h0, h100, h4, h9, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h100, h9, h94, h96, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h4, h7, h94, h95, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h9, h92, h94, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                    · linarith only [h107, h92, h93, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                      · linarith only [h0, h109, h4, h9, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h105, h109, h9, h92, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h105, h106, h4, h7, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h105, h9, h92, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h0, h114, h118, h119, h4, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h114, h116, h118, h119, h3, h92, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1, h115, h118, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h114, h117, h92, hlam]
                  · linarith only [h0, h115, h116, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                  · linarith only [h115, h125, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h114, h125, h9, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                            · rcases h1bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                rcases p135_3 (m.d 0 1) (by simp) with h137 | h137
                                · rcases p135_3 (m.d 1 2) (by simp) with h138 | h138
                                  · linarith only [h138, hlam, p135_0]
                                  · rcases p135_3 (m.d 1 3) (by simp) with h140 | h140
                                    · linarith only [h1, h140, hlam]
                                    · linarith only [h140, h9, hlam]
                                · linarith only [h137, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h128, h134, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1, u3ehi4]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                rcases p135_3 (m.d 0 1) (by simp) with h145 | h145
                                · rcases p135_3 (m.d 1 2) (by simp) with h146 | h146
                                  · linarith only [h0, h146, hlam]
                                  · rcases p135_3 (m.d 1 3) (by simp) with h148 | h148
                                    · linarith only [h1, h148, hlam]
                                    · linarith only [h128, h148, hlam]
                                · linarith only [h145, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                rcases p135_3 (m.d 0 1) (by simp) with h152 | h152
                                · rcases p135_3 (m.d 1 2) (by simp) with h153 | h153
                                  · linarith only [h0, h153, hlam]
                                  · rcases p135_3 (m.d 1 3) (by simp) with h155 | h155
                                    · linarith only [h1, h155, hlam]
                                    · linarith only [h129, h155, hlam]
                                · linarith only [h152, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h0, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h9, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h92, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h114, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h1, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                rcases p135_3 (m.d 0 1) (by simp) with h165 | h165
                                · rcases p135_3 (m.d 1 2) (by simp) with h166 | h166
                                  · linarith only [h166, h9, hlam]
                                  · rcases p135_3 (m.d 1 3) (by simp) with h168 | h168
                                    · rcases p135_3 (m.d 1 4) (by simp) with h169 | h169
                                      · linarith only [h128, h169, hlam]
                                      · linarith only [h169, h92, hlam]
                                    · linarith only [h168, h9, hlam]
                                · linarith only [h0, h165, hlam]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h0, h128, h134, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1, u3ehi4]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h0, h129, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1, u3ehi4]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h2, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                rcases p135_3 (m.d 0 1) (by simp) with h178 | h178
                                · rcases p135_3 (m.d 1 2) (by simp) with h179 | h179
                                  · linarith only [h179, h92, hlam]
                                  · rcases p135_3 (m.d 1 3) (by simp) with h181 | h181
                                    · rcases p135_3 (m.d 1 4) (by simp) with h182 | h182
                                      · rcases p135_3 (m.d 1 5) (by simp) with h183 | h183
                                        · linarith only [h130, h183, hlam]
                                        · linarith only [h114, h183, hlam]
                                      · linarith only [h182, h92, hlam]
                                    · linarith only [h181, h9, hlam]
                                · linarith only [h0, h178, hlam]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h128, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h0, h128, h129, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1, u3ehi4]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h3, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                rcases p135_3 (m.d 0 1) (by simp) with h193 | h193
                                · rcases p135_3 (m.d 1 2) (by simp) with h194 | h194
                                  · linarith only [h114, h194, hlam]
                                  · rcases p135_3 (m.d 1 3) (by simp) with h196 | h196
                                    · rcases p135_3 (m.d 1 4) (by simp) with h197 | h197
                                      · rcases p135_3 (m.d 1 5) (by simp) with h198 | h198
                                        · rcases h5bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p135_1, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h114, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p135_1, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1, u3ehi4]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            rcases p199_3 (m.d 0 5) (by simp) with h204 | h204
                                            · rcases p199_3 (m.d 1 5) (by simp) with h205 | h205
                                              · linarith only [h205, h3, hlam]
                                              · linarith only [h130, h205, hlam]
                                            · linarith only [h204, h8, hlam]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h3, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h114, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p199_1, u3ehi4]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h128, h130, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h5, hlam, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p135_1, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h132, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1, u3ehi4]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h131, h133, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h7, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h129, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h132, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h0, h134, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p199_1]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h8, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h130, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h133, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [h134, hlam, p199_0]
                                          · have p199_0 := h199c.1
                                            have p199_1 := h199c.2.1
                                            have p199_2 := h199c.2.2.1
                                            have p199_3 := h199c.2.2.2
                                            linarith only [hlam, p199_0]
                                        · linarith only [h114, h198, hlam]
                                      · linarith only [h197, h92, hlam]
                                    · linarith only [h196, h9, hlam]
                                · linarith only [h0, h193, hlam]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h129, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [h130, hlam, p135_0]
                              · have p135_0 := h135c.1
                                have p135_1 := h135c.2.1
                                have p135_2 := h135c.2.2.1
                                have p135_3 := h135c.2.2.2
                                linarith only [hlam, p135_0]
                            · linarith only [h0, h128, h130, h134, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h128, h130, h133, h4, h9, h92, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h129, h132, h9, hlam]
                      · linarith only [h129, h131, h9, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                          · linarith only [h0, h128, h130, h240, h242, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
                            · linarith only [h128, h242, h244, h92, hlam]
                            · rcases h1bigk with h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c | h246c
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h0, h242, h4, h6, h8, h92, hlam, p246_2]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h129, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1, u3ehi4]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                rcases p246_3 (m.d 0 1) (by simp) with h250 | h250
                                · rcases p246_3 (m.d 1 2) (by simp) with h251 | h251
                                  · linarith only [h0, h251, hlam]
                                  · rcases p246_3 (m.d 1 3) (by simp) with h253 | h253
                                    · linarith only [h1, h253, hlam]
                                    · linarith only [h128, h253, hlam]
                                · linarith only [h250, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                rcases p246_3 (m.d 0 1) (by simp) with h257 | h257
                                · rcases p246_3 (m.d 1 2) (by simp) with h258 | h258
                                  · linarith only [h0, h258, hlam]
                                  · rcases p246_3 (m.d 1 3) (by simp) with h260 | h260
                                    · linarith only [h1, h260, hlam]
                                    · linarith only [h129, h260, hlam]
                                · linarith only [h257, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h0, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h9, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h92, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h114, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h1, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                rcases p246_3 (m.d 0 1) (by simp) with h270 | h270
                                · rcases p246_3 (m.d 1 2) (by simp) with h271 | h271
                                  · linarith only [h271, h9, hlam]
                                  · rcases p246_3 (m.d 1 3) (by simp) with h273 | h273
                                    · rcases p246_3 (m.d 1 4) (by simp) with h274 | h274
                                      · linarith only [h128, h274, hlam]
                                      · linarith only [h274, h92, hlam]
                                    · linarith only [h273, h9, hlam]
                                · linarith only [h0, h270, hlam]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h0, h128, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1, u3ehi3]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h0, h129, h244, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1, u3ehi3]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h2, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h0, h242, h4, h6, h8, h92, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p246_1]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h128, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h130, hlam, p246_1]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h3, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                rcases p246_3 (m.d 0 1) (by simp) with h288 | h288
                                · rcases p246_3 (m.d 1 2) (by simp) with h289 | h289
                                  · linarith only [h114, h289, hlam]
                                  · rcases p246_3 (m.d 1 3) (by simp) with h291 | h291
                                    · rcases p246_3 (m.d 1 4) (by simp) with h292 | h292
                                      · linarith only [h130, h292, hlam]
                                      · linarith only [h292, h92, hlam]
                                    · linarith only [h291, h9, hlam]
                                · linarith only [h0, h288, hlam]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h129, hlam, p246_0]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [h128, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p246_1, u3ehi3]
                              · have p246_0 := h246c.1
                                have p246_1 := h246c.2.1
                                have p246_2 := h246c.2.2.1
                                have p246_3 := h246c.2.2.2
                                linarith only [hlam, p246_0]
                        · linarith only [h0, h128, h241, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h128, h240, h9, hlam]
                  · linarith only [h128, h129, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h303 | h303
                  · linarith only [h0, h128, h303, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                      · linarith only [h0, h128, h306, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                        · linarith only [h303, h306, h308, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h310 | h310
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                            · rcases h1bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h308, h311, h4, h6, h9, hlam, p312_2]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                rcases p312_3 (m.d 0 1) (by simp) with h315 | h315
                                · rcases p312_3 (m.d 1 2) (by simp) with h316 | h316
                                  · linarith only [h0, h316, hlam]
                                  · rcases p312_3 (m.d 1 3) (by simp) with h318 | h318
                                    · linarith only [h318, hlam, p312_0]
                                    · rcases p312_3 (m.d 1 4) (by simp) with h320 | h320
                                      · linarith only [h2, h320, hlam]
                                      · linarith only [h128, h320, hlam]
                                · linarith only [h315, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                rcases p312_3 (m.d 0 1) (by simp) with h324 | h324
                                · rcases p312_3 (m.d 1 2) (by simp) with h325 | h325
                                  · linarith only [h0, h325, hlam]
                                  · rcases p312_3 (m.d 1 3) (by simp) with h327 | h327
                                    · linarith only [h1, h327, hlam]
                                    · rcases p312_3 (m.d 1 4) (by simp) with h329 | h329
                                      · linarith only [h329, hlam, p312_0]
                                      · rcases p312_3 (m.d 1 5) (by simp) with h331 | h331
                                        · linarith only [h3, h331, hlam]
                                        · rcases h5bigk with h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c | h333c
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h303, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p333_1, u3ehi1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h114, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h308, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p333_1, u3ehi2]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            rcases p333_3 (m.d 0 5) (by simp) with h338 | h338
                                            · rcases p333_3 (m.d 1 5) (by simp) with h339 | h339
                                              · linarith only [h3, h339, hlam]
                                              · linarith only [h305, h339, hlam]
                                            · linarith only [h338, h8, hlam]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h3, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h114, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h303, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h5, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h308, hlam, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h7, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h303, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p333_1, u3ehi1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h0, h311, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p333_1]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h8, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h305, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h310, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [h311, hlam, p333_0]
                                          · have p333_0 := h333c.1
                                            have p333_1 := h333c.2.1
                                            have p333_2 := h333c.2.2.1
                                            have p333_3 := h333c.2.2.2
                                            linarith only [hlam, p333_0]
                                · linarith only [h324, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                rcases p312_3 (m.d 0 1) (by simp) with h364 | h364
                                · rcases p312_3 (m.d 1 2) (by simp) with h365 | h365
                                  · linarith only [h0, h365, hlam]
                                  · rcases p312_3 (m.d 1 3) (by simp) with h367 | h367
                                    · linarith only [h1, h367, hlam]
                                    · rcases p312_3 (m.d 1 4) (by simp) with h369 | h369
                                      · linarith only [h2, h369, hlam]
                                      · linarith only [h305, h369, hlam]
                                · linarith only [h364, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h9, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h92, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h114, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h1, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h128, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h128, hlam, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h303, hlam, p312_1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h2, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                rcases p312_3 (m.d 0 1) (by simp) with h384 | h384
                                · rcases p312_3 (m.d 1 2) (by simp) with h385 | h385
                                  · linarith only [h385, h92, hlam]
                                  · rcases p312_3 (m.d 1 3) (by simp) with h387 | h387
                                    · linarith only [h128, h387, hlam]
                                    · linarith only [h387, h9, hlam]
                                · linarith only [h0, h384, hlam]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p312_1, u3ehi1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h0, h128, h303, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p312_1, u3ehi1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h3, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                rcases p312_3 (m.d 0 1) (by simp) with h395 | h395
                                · rcases p312_3 (m.d 1 2) (by simp) with h396 | h396
                                  · linarith only [h114, h396, hlam]
                                  · rcases p312_3 (m.d 1 3) (by simp) with h398 | h398
                                    · linarith only [h303, h398, hlam]
                                    · linarith only [h398, h9, hlam]
                                · linarith only [h0, h395, hlam]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p312_1, u3ehi1]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [h305, hlam, p312_0]
                              · have p312_0 := h312c.1
                                have p312_1 := h312c.2.1
                                have p312_2 := h312c.2.2.1
                                have p312_3 := h312c.2.2.2
                                linarith only [hlam, p312_0]
                            · linarith only [h0, h128, h311, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h305, h310, h92, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h407 | h407
                      · linarith only [h0, h128, h4, h407, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
                        · linarith only [h407, h409, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h411 | h411
                          · linarith only [h0, h128, h305, h4, h407, h411, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h413 | h413
                            · linarith only [h0, h4, h407, h411, h413, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h0, h128, h4, h413, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
          · rcases m.htr 1 2 4 (by decide) (by decide) with h417 | h417
            · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
              · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
                · rcases m.htr 1 3 5 (by decide) (by decide) with h420 | h420
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h2, h421, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h423 | h423
                      · linarith only [h0, h416, h423, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h419, h423, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h419, h420, hc35, hlam, hphi, u3ehi3]
                · linarith only [h419, h6, h8, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h416, h418, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h2, h416, h417, h8, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
            · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
              · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                    · linarith only [h2, h434, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h436 | h436
                      · linarith only [h0, h4, h416, h430, h436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h416, h431, h433, h436, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h432, h433, hc35, hlam, hphi, u3ehi3]
                · linarith only [h432, h6, h8, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                · rcases m.htr 1 3 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h430, h431, h443, h5, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h445 | h445
                      · linarith only [h0, h4, h416, h430, h445, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h416, h442, h445, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h441, h442, hc35, hlam, hphi, u3ehi3]
                · linarith only [h441, h6, h8, hc45, hlam, hphi, ht34, u3ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h450 | h450
              · rcases m.htr 1 3 4 (by decide) (by decide) with h451 | h451
                · rcases m.htr 1 3 5 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h453 | h453
                    · linarith only [h2, h453, h8, hlam]
                    · linarith only [h430, h450, h453, hlam]
                  · linarith only [h451, h452, hc35, hlam, hphi, u3ehi3]
                · linarith only [h451, h6, h8, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h458 | h458
                · rcases m.htr 1 3 5 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h460 | h460
                    · linarith only [h2, h460, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h462 | h462
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h463 | h463
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h464 | h464
                          · linarith only [h0, h4, h462, h464, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h466 | h466
                            · linarith only [h2, h458, h466, h8, hlam]
                            · rcases h1bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h470 | h470
                                · rcases p468_3 (m.d 1 2) (by simp) with h471 | h471
                                  · linarith only [h471, hlam, p468_0]
                                  · rcases p468_3 (m.d 1 3) (by simp) with h473 | h473
                                    · linarith only [h1, h473, hlam]
                                    · linarith only [h416, h473, hlam]
                                · linarith only [h470, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h458, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1, u3ehi3]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h478 | h478
                                · rcases p468_3 (m.d 1 2) (by simp) with h479 | h479
                                  · linarith only [h0, h479, hlam]
                                  · rcases p468_3 (m.d 1 3) (by simp) with h481 | h481
                                    · linarith only [h1, h481, hlam]
                                    · linarith only [h458, h481, hlam]
                                · linarith only [h478, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h485 | h485
                                · rcases p468_3 (m.d 1 2) (by simp) with h486 | h486
                                  · linarith only [h0, h486, hlam]
                                  · rcases p468_3 (m.d 1 3) (by simp) with h488 | h488
                                    · linarith only [h1, h488, hlam]
                                    · linarith only [h459, h488, hlam]
                                · linarith only [h485, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h0, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h416, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h430, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h450, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h1, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h498 | h498
                                · rcases p468_3 (m.d 1 2) (by simp) with h499 | h499
                                  · linarith only [h416, h499, hlam]
                                  · rcases p468_3 (m.d 1 3) (by simp) with h501 | h501
                                    · rcases p468_3 (m.d 1 4) (by simp) with h502 | h502
                                      · linarith only [h458, h502, hlam]
                                      · linarith only [h430, h502, hlam]
                                    · linarith only [h416, h501, hlam]
                                · linarith only [h0, h498, hlam]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h0, h4, h416, h458, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1, u3ehi3]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h0, h4, h416, h458, h460, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1, u3ehi3]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h2, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p468_1]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h458, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h460, hlam, p468_1]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h3, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                rcases p468_3 (m.d 0 1) (by simp) with h516 | h516
                                · rcases p468_3 (m.d 1 2) (by simp) with h517 | h517
                                  · linarith only [h450, h517, hlam]
                                  · rcases p468_3 (m.d 1 3) (by simp) with h519 | h519
                                    · rcases p468_3 (m.d 1 4) (by simp) with h520 | h520
                                      · linarith only [h460, h520, hlam]
                                      · linarith only [h430, h520, hlam]
                                    · linarith only [h416, h519, hlam]
                                · linarith only [h0, h516, hlam]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h459, hlam, p468_0]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [h0, h4, h416, h458, h459, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1, u3ehi3]
                              · have p468_0 := h468c.1
                                have p468_1 := h468c.2.1
                                have p468_2 := h468c.2.2.1
                                have p468_3 := h468c.2.2.2
                                linarith only [hlam, p468_0]
                        · linarith only [h416, h459, h463, hlam]
                      · linarith only [h416, h459, h462, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h458, h459, hc35, hlam, hphi, u3ehi3]
                · linarith only [h458, h6, h8, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h533 | h533
      · linarith only [h533, h6, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
        · rcases m.htr 1 2 3 (by decide) (by decide) with h536 | h536
          · rcases m.htr 1 2 4 (by decide) (by decide) with h537 | h537
            · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
              · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                · linarith only [h1, h539, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h541 | h541
                  · linarith only [h1, h533, h541, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                      · linarith only [h1, h536, h544, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h546 | h546
                        · linarith only [h1, h533, h536, h546, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h548 | h548
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                            · rcases h1bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h537, h546, h548, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                rcases p550_3 (m.d 0 1) (by simp) with h553 | h553
                                · rcases p550_3 (m.d 1 2) (by simp) with h554 | h554
                                  · linarith only [h0, h554, hlam]
                                  · linarith only [h536, h554, hlam]
                                · linarith only [h553, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                rcases p550_3 (m.d 0 1) (by simp) with h558 | h558
                                · rcases p550_3 (m.d 1 2) (by simp) with h559 | h559
                                  · linarith only [h0, h559, hlam]
                                  · linarith only [h537, h559, hlam]
                                · linarith only [h558, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                rcases p550_3 (m.d 0 1) (by simp) with h563 | h563
                                · rcases p550_3 (m.d 1 2) (by simp) with h564 | h564
                                  · linarith only [h0, h564, hlam]
                                  · linarith only [h538, h564, hlam]
                                · linarith only [h563, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h0, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h0, h536, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h0, h537, h546, h548, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h0, h538, h546, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h1, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h536, hlam, p550_1]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h539, hlam, p550_1]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h541, hlam, p550_1]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h2, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h537, hlam, p550_1]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h2, h536, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h0, h537, h538, h546, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h3, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h538, hlam, p550_1]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h3, h536, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p550_1, u3ehi2]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [h543, hlam, p550_0]
                              · have p550_0 := h550c.1
                                have p550_1 := h550c.2.1
                                have p550_2 := h550c.2.2.1
                                have p550_3 := h550c.2.2.2
                                linarith only [hlam, p550_0]
                            · linarith only [h1, h536, h548, h549, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h2, h543, h544, h548, h6, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h535, h536, h539, h543, h6, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h5, h536, h538, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
              · rcases m.htr 1 3 4 (by decide) (by decide) with h593 | h593
                · linarith only [h1, h533, h593, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
                  · linarith only [h1, h595, h6, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h598 | h598
                      · linarith only [h0, h4, h598, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h536, h537, h598, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h536, h537, h597, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h5, h536, h592, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
            · rcases m.htr 1 2 5 (by decide) (by decide) with h604 | h604
              · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                · linarith only [h1, h533, h605, hc35, hlam, hphi, u3ehi3]
                · linarith only [h4, h533, h536, h603, h605, hc35, hlam, hphi, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                · linarith only [h4, h536, h6, h603, h608, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h4, h533, h536, h603, h608, hc35, hlam, hphi, u3ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h611 | h611
              · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                · linarith only [h4, h536, h6, h611, h612, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h614 | h614
                  · linarith only [h4, h533, h536, h611, h614, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h4, h536, h6, h611, h614, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h617 | h617
                · linarith only [h1, h4, h536, h6, h617, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h4, h533, h536, h603, h617, h619, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h621 | h621
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                      · linarith only [h4, h6, h622, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h624 | h624
                        · linarith only [h4, h533, h624, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h627 | h627
                            · rcases h1bigk with h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                rcases p628_3 (m.d 0 1) (by simp) with h630 | h630
                                · rcases p628_3 (m.d 1 2) (by simp) with h631 | h631
                                  · linarith only [h631, hlam, p628_0]
                                  · rcases p628_3 (m.d 1 3) (by simp) with h633 | h633
                                    · linarith only [h1, h633, hlam]
                                    · linarith only [h536, h633, hlam]
                                · linarith only [h630, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                rcases p628_3 (m.d 0 1) (by simp) with h637 | h637
                                · rcases p628_3 (m.d 1 2) (by simp) with h638 | h638
                                  · linarith only [h0, h638, hlam]
                                  · rcases p628_3 (m.d 1 3) (by simp) with h640 | h640
                                    · linarith only [h640, hlam, p628_0]
                                    · rcases p628_3 (m.d 1 4) (by simp) with h642 | h642
                                      · linarith only [h2, h642, hlam]
                                      · linarith only [h617, h642, hlam]
                                · linarith only [h637, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                rcases p628_3 (m.d 0 1) (by simp) with h646 | h646
                                · rcases p628_3 (m.d 1 2) (by simp) with h647 | h647
                                  · linarith only [h0, h647, hlam]
                                  · rcases p628_3 (m.d 1 3) (by simp) with h649 | h649
                                    · linarith only [h1, h649, hlam]
                                    · rcases p628_3 (m.d 1 4) (by simp) with h651 | h651
                                      · linarith only [h651, hlam, p628_0]
                                      · rcases p628_3 (m.d 1 5) (by simp) with h653 | h653
                                        · linarith only [h3, h653, hlam]
                                        · rcases h5bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h535, h619, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1, u3ehi1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h2, h535, h611, h619, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p655_1, u3ehi1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h533, hlam, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            rcases p655_3 (m.d 0 5) (by simp) with h660 | h660
                                            · rcases p655_3 (m.d 1 5) (by simp) with h661 | h661
                                              · linarith only [h3, h661, hlam]
                                              · linarith only [h621, h661, hlam]
                                            · linarith only [h535, h660, hlam]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h3, hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h611, hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h619, hlam, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h5, hlam, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h624, hlam, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h3, h619, h627, hc34, hlam, hphi, p655_1, u3ehi1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h619, h627, hc34, hlam, hphi, p655_1, u3ehi1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h611, h627, hc12, hc34, hlam, hphi, ht23, p655_1]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            rcases p655_3 (m.d 0 5) (by simp) with h679 | h679
                                            · linarith only [h533, h679, hlam]
                                            · linarith only [h535, h679, hlam]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h535, hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h621, hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h626, hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [h627, hlam, p655_0]
                                          · have p655_0 := h655c.1
                                            have p655_1 := h655c.2.1
                                            have p655_2 := h655c.2.2.1
                                            have p655_3 := h655c.2.2.2
                                            linarith only [hlam, p655_0]
                                · linarith only [h646, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                rcases p628_3 (m.d 0 1) (by simp) with h688 | h688
                                · rcases p628_3 (m.d 1 2) (by simp) with h689 | h689
                                  · linarith only [h0, h689, hlam]
                                  · rcases p628_3 (m.d 1 3) (by simp) with h691 | h691
                                    · linarith only [h1, h691, hlam]
                                    · rcases p628_3 (m.d 1 4) (by simp) with h693 | h693
                                      · linarith only [h2, h693, hlam]
                                      · linarith only [h621, h693, hlam]
                                · linarith only [h688, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h0, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h536, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h603, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h611, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h1, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h1, h533, h627, hc12, hc34, hlam, hphi, ht23, p628_1]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h617, hlam, p628_1]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h619, hlam, p628_1]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h2, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                rcases p628_3 (m.d 0 1) (by simp) with h708 | h708
                                · rcases p628_3 (m.d 1 2) (by simp) with h709 | h709
                                  · linarith only [h603, h709, hlam]
                                  · rcases p628_3 (m.d 1 3) (by simp) with h711 | h711
                                    · linarith only [h617, h711, hlam]
                                    · linarith only [h536, h711, hlam]
                                · linarith only [h0, h708, hlam]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p628_1, u3ehi1]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h2, h6, h619, hc34, hlam, hphi, p628_1, u3ehi1]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h3, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                rcases p628_3 (m.d 0 1) (by simp) with h719 | h719
                                · rcases p628_3 (m.d 1 2) (by simp) with h720 | h720
                                  · linarith only [h611, h720, hlam]
                                  · rcases p628_3 (m.d 1 3) (by simp) with h722 | h722
                                    · linarith only [h619, h722, hlam]
                                    · linarith only [h536, h722, hlam]
                                · linarith only [h0, h719, hlam]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h5, h533, h611, hc35, hlam, hphi, p628_1, u3ehi1]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [h621, hlam, p628_0]
                              · have p628_0 := h628c.1
                                have p628_1 := h628c.2.1
                                have p628_2 := h628c.2.2.1
                                have p628_3 := h628c.2.2.2
                                linarith only [hlam, p628_0]
                            · linarith only [h4, h536, h6, h627, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h2, h603, h621, h626, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h535, h6, h617, h621, hc34, hlam, hphi, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h732 | h732
          · rcases m.htr 1 2 4 (by decide) (by decide) with h733 | h733
            · rcases m.htr 1 2 5 (by decide) (by decide) with h734 | h734
              · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                · linarith only [h1, h6, h735, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h737 | h737
                  · linarith only [h1, h535, h6, h737, hc45, hlam, hphi, ht34, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                    · linarith only [h2, h535, h739, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h741 | h741
                      · linarith only [h4, h535, h6, h741, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h743 | h743
                        · linarith only [h533, h733, h741, h743, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h745 | h745
                          · linarith only [h0, h535, h733, h745, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                            · linarith only [h1, h535, h6, h732, h747, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1, h6, h732, h747, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h5, h732, h734, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h2, h535, h732, h733, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
            · linarith only [h4, h535, h6, h732, h752, hc24, hc45, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
              · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
                · linarith only [h4, h6, h732, h755, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h757 | h757
                  · linarith only [h4, h535, h6, h732, h757, hc45, hlam, hphi, ht34, u3ehi4]
                  · linarith only [h4, h535, h6, h732, h754, h757, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                · linarith only [h1, h6, h760, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                  · linarith only [h4, h6, h732, h762, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                    · linarith only [h2, h535, h764, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h766 | h766
                      · linarith only [h4, h535, h6, h766, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h768 | h768
                        · linarith only [h4, h533, h768, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                          · linarith only [h4, h535, h6, h732, h770, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h772 | h772
                            · linarith only [h4, h535, h6, h732, h772, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h4, h6, h732, h772, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h775 | h775
    · rcases m.htr 0 3 5 (by decide) (by decide) with h776 | h776
      · linarith only [h4, h5, h776, hlam]
      · linarith only [h775, h776, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h779 | h779
      · linarith only [h775, h779, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
        · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
          · rcases m.htr 1 2 4 (by decide) (by decide) with h783 | h783
            · rcases m.htr 1 2 5 (by decide) (by decide) with h784 | h784
              · linarith only [h0, h5, h784, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                · linarith only [h1, h775, h786, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h788 | h788
                  · linarith only [h2, h4, h5, h779, h786, h788, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h790 | h790
                    · linarith only [h783, h784, h790, hlam]
                    · linarith only [h775, h781, h786, h790, hc34, hlam, hphi, u3ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h793 | h793
              · linarith only [h0, h5, h793, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
                · linarith only [h1, h775, h795, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h797 | h797
                  · linarith only [h0, h1, h5, h779, h782, h797, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h800 | h800
                      · linarith only [h0, h5, h775, h782, h800, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h782, h783, h800, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h775, h781, h782, h783, h799, hc34, hlam, hphi, u3ehi2]
          · linarith only [h4, h5, h782, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
          · rcases m.htr 1 2 4 (by decide) (by decide) with h806 | h806
            · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
              · linarith only [h0, h5, h807, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
                · linarith only [h1, h775, h809, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h811 | h811
                  · linarith only [h1, h775, h781, h811, hc45, hlam, hphi, ht34, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h813 | h813
                    · linarith only [h2, h781, h813, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
                      · linarith only [h0, h805, h815, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h817 | h817
                        · linarith only [h0, h5, h779, h806, h815, h817, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h4, h5, h817, hc35, hlam, hphi, u3ehi2]
            · linarith only [h2, h781, h805, h806, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h4, h5, h805, hc12, hc25, hlam, hphi]

end R2N4
