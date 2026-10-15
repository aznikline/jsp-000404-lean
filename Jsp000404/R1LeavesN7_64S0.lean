import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_IR_L_I_L_R_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.2.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h12, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h15, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h15, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h10, h9, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h1, h19, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                        · linarith only [h22, h6, h9, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                          · linarith only [h0, h24, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h2, h21, h24, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                        · linarith only [h1, h21, h27, h4, h5, h6, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h21, h29, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                            · linarith only [h21, h31, h6, h9, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h31, h6, h9, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h35, h6, h8, hlam]
                    · linarith only [h34, h35, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h1, h34, h38, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                      · linarith only [h40, h7, h8, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                        · linarith only [h0, h42, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                          · linarith only [h40, h44, h7, h8, hlam]
                          · linarith only [h1, h4, h42, h44, h5, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                  · linarith only [h48, h6, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h50 | h50
                    · linarith only [h1, h4, h48, h50, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                        · linarith only [h48, h53, h6, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h1, h4, h53, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1, h4, h5, h52, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                  · linarith only [h57, h6, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h1, h4, h57, h59, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                        · linarith only [h57, h6, h62, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h1, h4, h6, h62, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1, h4, h5, h6, h61, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
              · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h6, h66, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h6, h66, h70, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h6, h66, h70, h71, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                          · linarith only [h66, h70, h77, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                            · linarith only [h66, h70, h76, h79, hlam]
                            · rcases h1bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h66, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h6, h66, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                rcases p81_3 (m.d 0 1) (by simp) with h85 | h85
                                · rcases p81_3 (m.d 1 2) (by simp) with h86 | h86
                                  · linarith only [h0, h86, hlam]
                                  · linarith only [h66, h86, hlam]
                                · linarith only [h85, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                rcases p81_3 (m.d 0 1) (by simp) with h90 | h90
                                · rcases p81_3 (m.d 1 2) (by simp) with h91 | h91
                                  · linarith only [h0, h91, hlam]
                                  · linarith only [h67, h91, hlam]
                                · linarith only [h90, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h6, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p81_1, u4ehi1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h6, h67, h76, h77, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h1, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h1, h66, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h1, h66, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h1, h67, h76, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h2, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h66, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h68, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h70, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h3, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h67, hlam, p81_1]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h69, hlam, p81_0]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [h3, h66, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p81_1, u3ehi3]
                              · have p81_0 := h81c.1
                                have p81_1 := h81c.2.1
                                have p81_2 := h81c.2.2.1
                                have p81_3 := h81c.2.2.2
                                linarith only [hlam, p81_0]
                        · linarith only [h1, h4, h6, h67, h76, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h68, h69, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h4, h6, h66, h68, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                      · linarith only [h120, h66, h67, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                          · linarith only [h120, h123, h66, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h1, h122, h123, h4, h5, h66, h67, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h122, h6, h66, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h118, h119, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h118, h4, h6, h66, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h129 | h129
                · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                            · linarith only [h1, h130, h135, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h129, h133, h134, h135, h66, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h1, h129, h134, h4, h5, h66, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1, h129, h131, h133, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h129, h132, h66, hlam]
                    · linarith only [h130, h131, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                    · linarith only [h1, h130, h142, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h129, h142, h6, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h150 | h150
                            · linarith only [h1, h145, h150, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h147, h150, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1, h145, h147, h149, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h1, h146, h148, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                            · linarith only [h145, h147, h157, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                            · rcases h1bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 1) (by simp) with h161 | h161
                                · rcases p159_3 (m.d 1 2) (by simp) with h162 | h162
                                  · linarith only [h162, hlam, p159_0]
                                  · rcases p159_3 (m.d 1 3) (by simp) with h164 | h164
                                    · linarith only [h1, h164, hlam]
                                    · linarith only [h164, h6, hlam]
                                · linarith only [h161, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h145, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1, u3ehi3]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 1) (by simp) with h169 | h169
                                · rcases p159_3 (m.d 1 2) (by simp) with h170 | h170
                                  · linarith only [h0, h170, hlam]
                                  · rcases p159_3 (m.d 1 3) (by simp) with h172 | h172
                                    · linarith only [h1, h172, hlam]
                                    · linarith only [h145, h172, hlam]
                                · linarith only [h169, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 1) (by simp) with h176 | h176
                                · rcases p159_3 (m.d 1 2) (by simp) with h177 | h177
                                  · linarith only [h0, h177, hlam]
                                  · rcases p159_3 (m.d 1 3) (by simp) with h179 | h179
                                    · linarith only [h1, h179, hlam]
                                    · linarith only [h146, h179, hlam]
                                · linarith only [h176, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h0, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h6, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h66, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h129, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h1, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                rcases p159_3 (m.d 0 1) (by simp) with h189 | h189
                                · rcases p159_3 (m.d 1 2) (by simp) with h190 | h190
                                  · linarith only [h190, h6, hlam]
                                  · rcases p159_3 (m.d 1 3) (by simp) with h192 | h192
                                    · rcases p159_3 (m.d 1 4) (by simp) with h193 | h193
                                      · linarith only [h145, h193, hlam]
                                      · linarith only [h193, h66, hlam]
                                    · linarith only [h192, h6, hlam]
                                · linarith only [h0, h189, hlam]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h1, h145, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1, u3ehi3]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h1, h145, h147, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p159_1, u3ehi3]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h2, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h147, h155, h156, hc12, hc23, hlam, hphi, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h145, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h147, hlam, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h3, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h147, h155, h156, hc12, hc23, hlam, hphi, p159_1]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h146, hlam, p159_0]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [h145, h147, h155, h156, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p159_1, u3ehi3]
                              · have p159_0 := h159c.1
                                have p159_1 := h159c.2.1
                                have p159_2 := h159c.2.2.1
                                have p159_3 := h159c.2.2.2
                                linarith only [hlam, p159_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                            · linarith only [h156, h211, h66, hc12, hc34, hlam, hphi, ht23]
                            · rcases h1bigk with h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c | h213c
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, h156, h4, h5, h66, hlam, p213_2]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h145, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p213_1, u3ehi3]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 1) (by simp) with h217 | h217
                                · rcases p213_3 (m.d 1 2) (by simp) with h218 | h218
                                  · linarith only [h0, h218, hlam]
                                  · rcases p213_3 (m.d 1 3) (by simp) with h220 | h220
                                    · linarith only [h1, h220, hlam]
                                    · linarith only [h145, h220, hlam]
                                · linarith only [h217, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 1) (by simp) with h224 | h224
                                · rcases p213_3 (m.d 1 2) (by simp) with h225 | h225
                                  · linarith only [h0, h225, hlam]
                                  · rcases p213_3 (m.d 1 3) (by simp) with h227 | h227
                                    · linarith only [h1, h227, hlam]
                                    · linarith only [h146, h227, hlam]
                                · linarith only [h224, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h0, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h6, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h66, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h129, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 1) (by simp) with h237 | h237
                                · rcases p213_3 (m.d 1 2) (by simp) with h238 | h238
                                  · linarith only [h238, h6, hlam]
                                  · rcases p213_3 (m.d 1 3) (by simp) with h240 | h240
                                    · rcases p213_3 (m.d 1 4) (by simp) with h241 | h241
                                      · linarith only [h145, h241, hlam]
                                      · linarith only [h241, h66, hlam]
                                    · linarith only [h240, h6, hlam]
                                · linarith only [h0, h237, hlam]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p213_1, u4ehi1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, h146, h211, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p213_1, u3ehi3]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h2, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h1, h156, h4, h5, h66, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p213_1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h145, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h147, hlam, p213_1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h3, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                rcases p213_3 (m.d 0 1) (by simp) with h255 | h255
                                · rcases p213_3 (m.d 1 2) (by simp) with h256 | h256
                                  · linarith only [h129, h256, hlam]
                                  · rcases p213_3 (m.d 1 3) (by simp) with h258 | h258
                                    · rcases p213_3 (m.d 1 4) (by simp) with h259 | h259
                                      · linarith only [h147, h259, hlam]
                                      · linarith only [h259, h66, hlam]
                                    · linarith only [h258, h6, hlam]
                                · linarith only [h0, h255, hlam]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h146, hlam, p213_0]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p213_1, u4ehi1]
                              · have p213_0 := h213c.1
                                have p213_1 := h213c.2.1
                                have p213_2 := h213c.2.2.1
                                have p213_3 := h213c.2.2.2
                                linarith only [hlam, p213_0]
                        · linarith only [h145, h155, h6, hlam]
                    · linarith only [h145, h146, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h269 | h269
                    · linarith only [h1, h145, h269, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h271 | h271
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h273 | h273
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h274 | h274
                            · rcases h1bigk with h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                rcases p275_3 (m.d 0 1) (by simp) with h277 | h277
                                · rcases p275_3 (m.d 1 2) (by simp) with h278 | h278
                                  · linarith only [h278, hlam, p275_0]
                                  · rcases p275_3 (m.d 1 3) (by simp) with h280 | h280
                                    · linarith only [h1, h280, hlam]
                                    · linarith only [h280, h6, hlam]
                                · linarith only [h277, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                rcases p275_3 (m.d 0 1) (by simp) with h284 | h284
                                · rcases p275_3 (m.d 1 2) (by simp) with h285 | h285
                                  · linarith only [h0, h285, hlam]
                                  · rcases p275_3 (m.d 1 3) (by simp) with h287 | h287
                                    · linarith only [h287, hlam, p275_0]
                                    · rcases p275_3 (m.d 1 4) (by simp) with h289 | h289
                                      · linarith only [h2, h289, hlam]
                                      · linarith only [h145, h289, hlam]
                                · linarith only [h284, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h271, hc01, hlam, hphi, ht0b, ht45, ht5b, p275_1, u4ehi4]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                rcases p275_3 (m.d 0 1) (by simp) with h294 | h294
                                · rcases p275_3 (m.d 1 2) (by simp) with h295 | h295
                                  · linarith only [h0, h295, hlam]
                                  · rcases p275_3 (m.d 1 3) (by simp) with h297 | h297
                                    · linarith only [h1, h297, hlam]
                                    · rcases p275_3 (m.d 1 4) (by simp) with h299 | h299
                                      · linarith only [h2, h299, hlam]
                                      · linarith only [h271, h299, hlam]
                                · linarith only [h294, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h0, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h6, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h66, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h129, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h1, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h269, h272, h274, hc12, hc24, hlam, hphi, p275_1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h145, hlam, p275_1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h269, hlam, p275_1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h2, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h145, h272, hc12, hc23, hlam, hphi, p275_1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h145, h272, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p275_1, u3ehi1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h129, h145, h272, hc12, hc23, hlam, hphi, p275_1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h3, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h145, h271, h272, hc12, hc23, hlam, hphi, p275_1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h269, hc35, hlam, hphi, p275_1, u3ehi1]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [h271, hlam, p275_0]
                              · have p275_0 := h275c.1
                                have p275_1 := h275c.2.1
                                have p275_2 := h275c.2.2.1
                                have p275_3 := h275c.2.2.2
                                linarith only [hlam, p275_0]
                            · linarith only [h1, h145, h274, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h145, h271, h272, h273, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                            · rcases h1bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h1, h272, h4, h6, hlam, p327_2]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 1) (by simp) with h330 | h330
                                · rcases p327_3 (m.d 1 2) (by simp) with h331 | h331
                                  · linarith only [h0, h331, hlam]
                                  · rcases p327_3 (m.d 1 3) (by simp) with h333 | h333
                                    · linarith only [h333, hlam, p327_0]
                                    · rcases p327_3 (m.d 1 4) (by simp) with h335 | h335
                                      · linarith only [h2, h335, hlam]
                                      · linarith only [h145, h335, hlam]
                                · linarith only [h330, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h271, hc01, hlam, hphi, ht0b, ht45, ht5b, p327_1, u4ehi4]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 1) (by simp) with h340 | h340
                                · rcases p327_3 (m.d 1 2) (by simp) with h341 | h341
                                  · linarith only [h0, h341, hlam]
                                  · rcases p327_3 (m.d 1 3) (by simp) with h343 | h343
                                    · linarith only [h1, h343, hlam]
                                    · rcases p327_3 (m.d 1 4) (by simp) with h345 | h345
                                      · linarith only [h2, h345, hlam]
                                      · linarith only [h271, h345, hlam]
                                · linarith only [h340, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h0, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h6, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h66, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h129, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h1, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h1, h272, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h145, hlam, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h269, hlam, p327_1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h2, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 1) (by simp) with h360 | h360
                                · rcases p327_3 (m.d 1 2) (by simp) with h361 | h361
                                  · linarith only [h361, h66, hlam]
                                  · rcases p327_3 (m.d 1 3) (by simp) with h363 | h363
                                    · linarith only [h145, h363, hlam]
                                    · linarith only [h363, h6, hlam]
                                · linarith only [h0, h360, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1, u3ehi1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h1, h269, h272, h4, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1, u3ehi1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h3, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                rcases p327_3 (m.d 0 1) (by simp) with h371 | h371
                                · rcases p327_3 (m.d 1 2) (by simp) with h372 | h372
                                  · linarith only [h129, h372, hlam]
                                  · rcases p327_3 (m.d 1 3) (by simp) with h374 | h374
                                    · linarith only [h269, h374, hlam]
                                    · linarith only [h374, h6, hlam]
                                · linarith only [h0, h371, hlam]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p327_1, u3ehi1]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [h271, hlam, p327_0]
                              · have p327_0 := h327c.1
                                have p327_1 := h327c.2.1
                                have p327_2 := h327c.2.2.1
                                have p327_3 := h327c.2.2.2
                                linarith only [hlam, p327_0]
                            · linarith only [h272, h326, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h271, h325, h66, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h385 | h385
                            · linarith only [h1, h271, h385, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · linarith only [h145, h383, h384, h385, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h1, h145, h383, h384, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                          · linarith only [h1, h271, h383, h389, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h391 | h391
                            · linarith only [h1, h145, h389, h391, h4, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h145, h391, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h394 | h394
            · rcases m.htr 1 2 4 (by decide) (by decide) with h395 | h395
              · rcases m.htr 1 2 5 (by decide) (by decide) with h396 | h396
                · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                      · linarith only [h399, h5, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                        · linarith only [h0, h394, h401, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h397, h401, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h397, h398, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h397, h4, h5, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                    · linarith only [h394, h396, h407, hlam]
                    · linarith only [h406, h407, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h4, h406, h5, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h2, h394, h395, h5, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h412 | h412
              · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
                · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
                      · linarith only [h2, h416, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                          · linarith only [h412, h419, h5, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                            · linarith only [h394, h413, h418, h419, h421, h5, hc23, hlam, hphi, ht01, ht12, u0ehi3]
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
                                linarith only [h413, h418, h419, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h415, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u3ehi4]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h427 | h427
                                · rcases p423_3 (m.d 1 2) (by simp) with h428 | h428
                                  · linarith only [h0, h428, hlam]
                                  · linarith only [h412, h428, hlam]
                                · linarith only [h427, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                rcases p423_3 (m.d 0 1) (by simp) with h432 | h432
                                · rcases p423_3 (m.d 1 2) (by simp) with h433 | h433
                                  · linarith only [h0, h433, hlam]
                                  · linarith only [h413, h433, hlam]
                                · linarith only [h432, hlam, p423_0]
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
                                linarith only [h394, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h394, h412, h418, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h394, h413, h418, h419, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h1, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h1, h412, h418, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h1, h412, h418, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h1, h413, h418, h419, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h2, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h412, hlam, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h414, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h416, hlam, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h3, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h413, hlam, p423_1]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h415, hlam, p423_0]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [h3, h412, h418, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u3ehi3]
                              · have p423_0 := h423c.1
                                have p423_1 := h423c.2.1
                                have p423_2 := h423c.2.2.1
                                have p423_3 := h423c.2.2.2
                                linarith only [hlam, p423_0]
                        · linarith only [h4, h418, h5, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h414, h415, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h4, h414, h5, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h462 | h462
                      · linarith only [h462, h5, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
                          · linarith only [h412, h465, h5, hc12, hlam, hphi, ht01, u0ehi3]
                          · linarith only [h412, h413, h465, hc45, hlam, hphi, u4ehi2]
                        · linarith only [h394, h412, h464, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h460, h461, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h4, h460, h5, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h471 | h471
                · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                      · linarith only [h2, h474, h5, hlam]
                      · linarith only [h412, h471, h474, hlam]
                    · linarith only [h472, h473, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h4, h472, h5, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h480 | h480
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                      · linarith only [h2, h481, h5, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h484 | h484
                          · linarith only [h483, h484, h5, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h486 | h486
                            · linarith only [h479, h484, h486, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                            · rcases h1bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h490 | h490
                                · rcases p488_3 (m.d 1 2) (by simp) with h491 | h491
                                  · linarith only [h491, hlam, p488_0]
                                  · rcases p488_3 (m.d 1 3) (by simp) with h493 | h493
                                    · linarith only [h1, h493, hlam]
                                    · linarith only [h394, h493, hlam]
                                · linarith only [h490, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h480, h486, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1, u3ehi3]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h498 | h498
                                · rcases p488_3 (m.d 1 2) (by simp) with h499 | h499
                                  · linarith only [h0, h499, hlam]
                                  · rcases p488_3 (m.d 1 3) (by simp) with h501 | h501
                                    · linarith only [h1, h501, hlam]
                                    · linarith only [h479, h501, hlam]
                                · linarith only [h498, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h505 | h505
                                · rcases p488_3 (m.d 1 2) (by simp) with h506 | h506
                                  · linarith only [h0, h506, hlam]
                                  · rcases p488_3 (m.d 1 3) (by simp) with h508 | h508
                                    · linarith only [h1, h508, hlam]
                                    · linarith only [h480, h508, hlam]
                                · linarith only [h505, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h0, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h394, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h412, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h471, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h518 | h518
                                · rcases p488_3 (m.d 1 2) (by simp) with h519 | h519
                                  · linarith only [h394, h519, hlam]
                                  · rcases p488_3 (m.d 1 3) (by simp) with h521 | h521
                                    · rcases p488_3 (m.d 1 4) (by simp) with h522 | h522
                                      · linarith only [h479, h522, hlam]
                                      · linarith only [h412, h522, hlam]
                                    · linarith only [h394, h521, hlam]
                                · linarith only [h0, h518, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, h479, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1, u3ehi3]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, h479, h481, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1, u3ehi3]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h2, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h2, h5, hc12, hc45, hlam, hphi, ht23, ht34, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h479, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h481, hlam, p488_1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h3, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                rcases p488_3 (m.d 0 1) (by simp) with h536 | h536
                                · rcases p488_3 (m.d 1 2) (by simp) with h537 | h537
                                  · linarith only [h471, h537, hlam]
                                  · rcases p488_3 (m.d 1 3) (by simp) with h539 | h539
                                    · rcases p488_3 (m.d 1 4) (by simp) with h540 | h540
                                      · linarith only [h481, h540, hlam]
                                      · linarith only [h412, h540, hlam]
                                    · linarith only [h394, h539, hlam]
                                · linarith only [h0, h536, hlam]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h480, hlam, p488_0]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [h1, h480, hc01, hlam, hphi, ht0b, ht45, ht5b, p488_1, u4ehi1]
                              · have p488_0 := h488c.1
                                have p488_1 := h488c.2.1
                                have p488_2 := h488c.2.2.1
                                have p488_3 := h488c.2.2.2
                                linarith only [hlam, p488_0]
                        · linarith only [h2, h394, h479, h483, h5, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h479, h480, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h4, h479, h5, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h551 | h551
          · rcases m.htr 1 2 3 (by decide) (by decide) with h552 | h552
            · rcases m.htr 1 2 4 (by decide) (by decide) with h553 | h553
              · rcases m.htr 1 2 5 (by decide) (by decide) with h554 | h554
                · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                  · linarith only [h1, h4, h555, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h557 | h557
                    · linarith only [h1, h4, h557, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h559 | h559
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
                        · linarith only [h4, h552, h560, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h562 | h562
                          · linarith only [h0, h553, h562, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h553, h559, h562, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h4, h551, h552, h555, h559, hc34, hlam, hphi, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h566 | h566
                  · linarith only [h1, h4, h566, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h568 | h568
                    · linarith only [h1, h4, h568, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h570 | h570
                      · linarith only [h553, h554, h570, hlam]
                      · linarith only [h4, h551, h566, h570, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h573 | h573
                · rcases m.htr 1 3 4 (by decide) (by decide) with h574 | h574
                  · linarith only [h4, h574, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                    · linarith only [h1, h4, h576, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h578 | h578
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                        · linarith only [h4, h552, h579, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h552, h553, h579, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h4, h551, h552, h553, h578, hc34, hlam, hphi, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                  · linarith only [h1, h4, h583, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h585 | h585
                    · linarith only [h1, h4, h585, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h588 | h588
                        · linarith only [h3, h4, h551, h552, h573, h588, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h552, h553, h588, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h4, h551, h552, h553, h587, hc34, hlam, hphi, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h592 | h592
              · rcases m.htr 1 2 5 (by decide) (by decide) with h593 | h593
                · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                  · linarith only [h1, h4, h594, hlam]
                  · linarith only [h552, h592, h594, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h597 | h597
                  · linarith only [h1, h4, h597, hlam]
                  · linarith only [h552, h592, h597, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                  · linarith only [h1, h4, h601, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                    · linarith only [h1, h4, h603, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h552, h600, h603, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h606 | h606
                  · linarith only [h1, h4, h606, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h608 | h608
                    · linarith only [h1, h4, h608, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                        · linarith only [h4, h611, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h613 | h613
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                            · rcases h1bigk with h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                rcases p615_3 (m.d 0 1) (by simp) with h617 | h617
                                · rcases p615_3 (m.d 1 2) (by simp) with h618 | h618
                                  · linarith only [h618, hlam, p615_0]
                                  · rcases p615_3 (m.d 1 3) (by simp) with h620 | h620
                                    · linarith only [h1, h620, hlam]
                                    · linarith only [h552, h620, hlam]
                                · linarith only [h617, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                rcases p615_3 (m.d 0 1) (by simp) with h624 | h624
                                · rcases p615_3 (m.d 1 2) (by simp) with h625 | h625
                                  · linarith only [h0, h625, hlam]
                                  · rcases p615_3 (m.d 1 3) (by simp) with h627 | h627
                                    · linarith only [h627, hlam, p615_0]
                                    · rcases p615_3 (m.d 1 4) (by simp) with h629 | h629
                                      · linarith only [h2, h629, hlam]
                                      · linarith only [h606, h629, hlam]
                                · linarith only [h624, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h610, hc01, hlam, hphi, ht0b, ht45, ht5b, p615_1, u4ehi4]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                rcases p615_3 (m.d 0 1) (by simp) with h634 | h634
                                · rcases p615_3 (m.d 1 2) (by simp) with h635 | h635
                                  · linarith only [h0, h635, hlam]
                                  · rcases p615_3 (m.d 1 3) (by simp) with h637 | h637
                                    · linarith only [h1, h637, hlam]
                                    · rcases p615_3 (m.d 1 4) (by simp) with h639 | h639
                                      · linarith only [h2, h639, hlam]
                                      · linarith only [h610, h639, hlam]
                                · linarith only [h634, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h0, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h552, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h592, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h600, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h1, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h608, hc12, hc35, hlam, hphi, ht23, p615_1]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h606, hlam, p615_1]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h608, hlam, p615_1]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h2, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                rcases p615_3 (m.d 0 1) (by simp) with h654 | h654
                                · rcases p615_3 (m.d 1 2) (by simp) with h655 | h655
                                  · linarith only [h592, h655, hlam]
                                  · rcases p615_3 (m.d 1 3) (by simp) with h657 | h657
                                    · linarith only [h606, h657, hlam]
                                    · linarith only [h552, h657, hlam]
                                · linarith only [h0, h654, hlam]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p615_1, u3ehi1]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h2, h608, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p615_1, u3ehi1]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h3, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                rcases p615_3 (m.d 0 1) (by simp) with h665 | h665
                                · rcases p615_3 (m.d 1 2) (by simp) with h666 | h666
                                  · linarith only [h600, h666, hlam]
                                  · rcases p615_3 (m.d 1 3) (by simp) with h668 | h668
                                    · linarith only [h608, h668, hlam]
                                    · linarith only [h552, h668, hlam]
                                · linarith only [h0, h665, hlam]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p615_1, u3ehi1]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [h610, hlam, p615_0]
                              · have p615_0 := h615c.1
                                have p615_1 := h615c.2.1
                                have p615_2 := h615c.2.2.1
                                have p615_3 := h615c.2.2.2
                                linarith only [hlam, p615_0]
                            · linarith only [h4, h614, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h2, h610, h613, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h4, h551, h606, h610, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h678 | h678
            · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
              · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
                · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
                  · linarith only [h1, h4, h681, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h683 | h683
                    · linarith only [h1, h4, h551, h683, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h685 | h685
                      · linarith only [h4, h551, h685, hc14, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h687 | h687
                        · linarith only [h4, h678, h687, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h689 | h689
                          · linarith only [h4, h551, h689, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h691 | h691
                            · linarith only [h4, h551, h691, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                            · linarith only [h4, h691, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h694 | h694
                  · linarith only [h1, h4, h694, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h696 | h696
                    · linarith only [h1, h4, h696, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h698 | h698
                      · linarith only [h2, h551, h698, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h700 | h700
                        · linarith only [h4, h678, h680, h700, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h702 | h702
                          · linarith only [h4, h551, h679, h680, h702, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                          · linarith only [h679, h680, h700, h702, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h2, h551, h678, h679, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
              · linarith only [h1, h4, h551, h678, h706, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h708 | h708
                · rcases m.htr 1 3 4 (by decide) (by decide) with h709 | h709
                  · linarith only [h1, h4, h551, h709, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h711 | h711
                    · linarith only [h1, h4, h551, h711, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h678, h708, h711, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h714 | h714
                  · linarith only [h1, h4, h714, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                    · linarith only [h1, h4, h551, h716, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                      · linarith only [h2, h551, h718, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h720 | h720
                        · linarith only [h4, h720, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h722 | h722
                          · linarith only [h4, h551, h722, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                            · linarith only [h4, h551, h724, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                            · linarith only [h4, h724, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h727 | h727
        · rcases m.htr 0 4 5 (by decide) (by decide) with h728 | h728
          · linarith only [h2, h3, h728, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
            · linarith only [h0, h3, h730, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
              · linarith only [h1, h3, h730, h732, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h734 | h734
                · linarith only [h1, h3, h730, h734, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h736 | h736
                  · linarith only [h1, h3, h734, h736, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1, h3, h727, h730, h734, h736, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h739 | h739
          · linarith only [h2, h3, h739, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h741 | h741
            · linarith only [h0, h3, h741, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h743 | h743
              · linarith only [h1, h3, h741, h743, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h745 | h745
                · linarith only [h1, h3, h741, h745, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
                  · linarith only [h1, h3, h745, h747, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
                    · linarith only [h2, h3, h745, h747, h749, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h2, h3, h747, h749, hc35, hlam, hphi, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h752 | h752
      · rcases m.htr 0 3 4 (by decide) (by decide) with h753 | h753
        · linarith only [h1, h2, h753, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h755 | h755
          · rcases m.htr 1 2 3 (by decide) (by decide) with h756 | h756
            · linarith only [h0, h2, h756, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
              · linarith only [h1, h2, h756, h758, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
                · rcases m.htr 1 3 4 (by decide) (by decide) with h761 | h761
                  · linarith only [h1, h2, h753, h758, h761, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1, h2, h761, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
                  · linarith only [h1, h2, h764, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h2, h764, hc34, hlam, hphi, u3ehi1]
          · linarith only [h1, h2, h755, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h768 | h768
        · linarith only [h1, h2, h768, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h770 | h770
          · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
            · linarith only [h0, h2, h771, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h773 | h773
              · linarith only [h1, h2, h771, h773, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h775 | h775
                · linarith only [h1, h752, h771, h775, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h777 | h777
                  · linarith only [h1, h2, h768, h773, h777, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1, h2, h777, hc34, hlam, hphi, u3ehi1]
          · linarith only [h1, h2, h770, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h781 | h781
    · rcases m.htr 0 1 5 (by decide) (by decide) with h782 | h782
      · rcases m.htr 0 3 4 (by decide) (by decide) with h783 | h783
        · rcases m.htr 0 4 5 (by decide) (by decide) with h784 | h784
          · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
            · linarith only [h0, h1, h785, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h787 | h787
              · linarith only [h0, h1, h785, h787, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h789 | h789
                · rcases m.htr 1 3 4 (by decide) (by decide) with h790 | h790
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h792 | h792
                      · linarith only [h1, h781, h785, h792, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h781, h784, h785, h787, h792, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h791, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1, h781, h783, h784, h790, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                      · linarith only [h1, h781, h785, h799, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h781, h784, h785, h799, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h1, h798, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1, h781, h784, h797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h804 | h804
            · linarith only [h0, h1, h804, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h806 | h806
              · linarith only [h0, h1, h804, h806, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h808 | h808
                · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h811 | h811
                      · linarith only [h1, h781, h784, h804, h811, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h806, h808, h811, hlam]
                    · linarith only [h1, h781, h806, h810, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h781, h809, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h817 | h817
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h818 | h818
                      · linarith only [h781, h784, h818, hc01, hlam, hphi, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h820 | h820
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h821 | h821
                          · linarith only [h784, h821, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h823 | h823
                            · linarith only [h1, h782, h784, h804, h816, h818, h823, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                            · rcases h1bigk with h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, h804, hc12, hc23, hlam, hphi, p825_1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, h804, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p825_1, u4ehi1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, h804, h808, hc12, hc23, hlam, hphi, p825_1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h0, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h804, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h806, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h808, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h804, hc23, hlam, hphi, ht01, ht12, p825_1, u0ehi0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                rcases p825_3 (m.d 0 1) (by simp) with h837 | h837
                                · linarith only [h1, h837, hlam]
                                · linarith only [h0, h837, hlam]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                rcases p825_3 (m.d 0 1) (by simp) with h841 | h841
                                · linarith only [h1, h841, hlam]
                                · linarith only [h781, h841, hlam]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                rcases p825_3 (m.d 0 1) (by simp) with h844 | h844
                                · linarith only [h1, h844, hlam]
                                · linarith only [h782, h844, hlam]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h781, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, h781, h804, hc12, hc23, hlam, hphi, p825_1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h816, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h818, hlam, p825_1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h782, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, h782, h804, hc12, hc23, hlam, hphi, p825_1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h817, hlam, p825_0]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [h1, h782, h804, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p825_1, u4ehi1]
                              · have p825_0 := h825c.1
                                have p825_1 := h825c.2.1
                                have p825_2 := h825c.2.2.1
                                have p825_3 := h825c.2.2.2
                                linarith only [hlam, p825_0]
                        · linarith only [h1, h804, h820, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h1, h781, h816, h817, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h781, h816, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
        · linarith only [h1, h781, h783, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h861 | h861
        · rcases m.htr 0 4 5 (by decide) (by decide) with h862 | h862
          · linarith only [h781, h782, h862, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h864 | h864
            · linarith only [h0, h1, h864, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
              · linarith only [h0, h1, h864, h866, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
                · linarith only [h781, h782, h866, h868, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h871 | h871
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h872 | h872
                      · linarith only [h781, h782, h862, h864, h871, h872, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h781, h782, h872, hc45, hlam, hphi, u4ehi1]
                    · linarith only [h1, h781, h870, h871, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h781, h870, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
        · linarith only [h1, h781, h861, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h878 | h878
      · rcases m.htr 0 3 4 (by decide) (by decide) with h879 | h879
        · rcases m.htr 0 4 5 (by decide) (by decide) with h880 | h880
          · rcases m.htr 1 2 3 (by decide) (by decide) with h881 | h881
            · linarith only [h0, h1, h881, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h883 | h883
              · linarith only [h0, h1, h881, h883, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h885 | h885
                · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h890 | h890
                          · linarith only [h0, h781, h881, h885, h886, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h781, h883, h890, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h781, h879, h881, h885, h886, h887, h889, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h781, h885, h887, h888, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h1, h879, h887, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h886, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h897 | h897
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h898 | h898
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h899 | h899
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h900 | h900
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h901 | h901
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
                            · rcases h1bigk with h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h781, h883, hc12, hc24, hlam, hphi, p903_1]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h1, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h781, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h781, h897, h898, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1, u3ehi4]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h0, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h881, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h883, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h885, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [hc13, hlam, hphi, ht01, p903_1, u0ehi0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                rcases p903_3 (m.d 0 1) (by simp) with h915 | h915
                                · linarith only [h1, h915, hlam]
                                · linarith only [h0, h915, hlam]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h781, h878, h881, h898, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p903_1, u3ehi4]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                rcases p903_3 (m.d 0 1) (by simp) with h920 | h920
                                · linarith only [h1, h920, hlam]
                                · linarith only [h878, h920, hlam]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h878, h898, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1, u3ehi4]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                rcases p903_3 (m.d 0 1) (by simp) with h924 | h924
                                · linarith only [h781, h924, hlam]
                                · linarith only [h0, h924, hlam]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h897, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                rcases p903_3 (m.d 0 1) (by simp) with h929 | h929
                                · linarith only [h781, h929, hlam]
                                · linarith only [h878, h929, hlam]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h878, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h1, h878, h881, hc12, hc23, hlam, hphi, p903_1]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h898, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [h899, hlam, p903_0]
                              · have p903_0 := h903c.1
                                have p903_1 := h903c.2.1
                                have p903_2 := h903c.2.2.1
                                have p903_3 := h903c.2.2.2
                                linarith only [hlam, p903_0]
                            · linarith only [h781, h878, h883, h899, h900, h902, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h781, h878, h883, h899, h901, hlam]
                        · linarith only [h1, h881, h900, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h781, h878, h898, h899, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h781, h897, h898, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1, h878, h879, h897, hc03, hlam, hphi, u0ehi4]
          · linarith only [h781, h878, h880, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h944 | h944
          · rcases m.htr 1 2 3 (by decide) (by decide) with h945 | h945
            · linarith only [h0, h781, h945, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h947 | h947
              · linarith only [h0, h1, h879, h947, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h949 | h949
                · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                  · linarith only [h0, h1, h879, h945, h950, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h949, h950, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h953 | h953
                  · linarith only [h1, h879, h953, hc13, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1, h878, h953, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
          · linarith only [h781, h878, h944, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h957 | h957
        · rcases m.htr 0 4 5 (by decide) (by decide) with h958 | h958
          · rcases m.htr 1 2 3 (by decide) (by decide) with h959 | h959
            · linarith only [h0, h1, h959, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h961 | h961
              · linarith only [h0, h1, h959, h961, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h963 | h963
                · linarith only [h0, h878, h963, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h965 | h965
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h966 | h966
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h968 | h968
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h969 | h969
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                            · rcases h1bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h878, h959, h965, h967, hc12, hc23, hlam, hphi, p971_1]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h1, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h781, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h878, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h0, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h959, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h961, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h963, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h959, hc23, hlam, hphi, ht01, ht12, p971_1, u0ehi0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                rcases p971_3 (m.d 0 1) (by simp) with h983 | h983
                                · linarith only [h1, h983, hlam]
                                · linarith only [h0, h983, hlam]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h0, h781, h959, hc23, hlam, hphi, ht01, ht12, p971_1, u0ehi1]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h0, h878, h959, hc23, hlam, hphi, ht01, ht12, p971_1, u0ehi1]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h0, hc14, hlam, hphi, ht01, p971_1, u0ehi1]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                rcases p971_3 (m.d 0 1) (by simp) with h990 | h990
                                · linarith only [h781, h990, hlam]
                                · linarith only [h0, h990, hlam]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h965, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h0, h878, h959, h965, hc23, hlam, hphi, ht01, ht12, p971_1, u0ehi1]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h0, hc15, hlam, hphi, ht01, p971_1, u0ehi1]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                rcases p971_3 (m.d 0 1) (by simp) with h997 | h997
                                · linarith only [h878, h997, hlam]
                                · linarith only [h0, h997, hlam]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h966, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [h967, hlam, p971_0]
                              · have p971_0 := h971c.1
                                have p971_1 := h971c.2.1
                                have p971_2 := h971c.2.2.1
                                have p971_3 := h971c.2.2.2
                                linarith only [hlam, p971_0]
                            · rcases h1bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h1, h959, hc12, hc23, hlam, hphi, p1003_1]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h1, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h781, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h878, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h0, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h959, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h961, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h963, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h959, hc23, hlam, hphi, ht01, ht12, p1003_1, u0ehi0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                rcases p1003_3 (m.d 0 1) (by simp) with h1015 | h1015
                                · linarith only [h1, h1015, hlam]
                                · linarith only [h0, h1015, hlam]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h781, h958, h959, h970, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1003_1, u4ehi3]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h0, h878, h959, hc23, hlam, hphi, ht01, ht12, p1003_1, u0ehi1]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h0, hc14, hlam, hphi, ht01, p1003_1, u0ehi1]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                rcases p1003_3 (m.d 0 1) (by simp) with h1022 | h1022
                                · linarith only [h1022, h781, hlam]
                                · linarith only [h0, h1022, hlam]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h965, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h0, h878, h961, h968, hc23, hlam, hphi, ht01, ht12, p1003_1, u0ehi1]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h0, hc15, hlam, hphi, ht01, p1003_1, u0ehi1]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                rcases p1003_3 (m.d 0 1) (by simp) with h1029 | h1029
                                · linarith only [h1029, h878, hlam]
                                · linarith only [h0, h1029, hlam]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h966, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [h967, hlam, p1003_0]
                              · have p1003_0 := h1003c.1
                                have p1003_1 := h1003c.2.1
                                have p1003_2 := h1003c.2.2.1
                                have p1003_3 := h1003c.2.2.2
                                linarith only [hlam, p1003_0]
                          · linarith only [h0, h781, h957, h958, h961, h969, hc03, hlam, hphi, u0ehi1]
                        · linarith only [h0, h1, h959, h968, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h0, h781, h958, h967, hc04, hlam, hphi, u0ehi1]
                    · linarith only [h1, h957, h966, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h957, h965, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1040 | h1040
            · linarith only [h0, h1, h1040, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1042 | h1042
              · linarith only [h0, h1042, h781, h958, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1044 | h1044
                · linarith only [h0, h1044, h878, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1046 | h1046
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1047 | h1047
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1048 | h1048
                      · linarith only [h0, h1048, h781, h958, hc14, hlam, hphi, ht01, u0ehi1]
                      · linarith only [h0, h1048, h781, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                    · linarith only [h0, h1, h1047, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h1, h1046, h957, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1054 | h1054
            · linarith only [h0, h1, h1054, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1056 | h1056
              · linarith only [h0, h1, h1056, h957, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1058 | h1058
                · linarith only [h0, h1058, h878, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1060 | h1060
                  · linarith only [h0, h1, h1054, h1060, h957, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1060, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1063 | h1063
            · linarith only [h0, h1, h1053, h1063, h957, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1065 | h1065
              · linarith only [h0, h1, h1053, h1065, h957, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1067 | h1067
                · linarith only [h0, h1067, h878, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                  · linarith only [h0, h1, h1069, h957, hc13, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h1, h1069, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

end R2N4
