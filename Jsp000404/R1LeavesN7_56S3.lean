import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                        · linarith only [h0, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h11, h12, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                    · linarith only [h0, h11, h2, h21, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                        · linarith only [h11, h24, h8, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                          · linarith only [h21, h26, h8, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                              · rcases h2bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  rcases p30_3 (m.d 0 2) (by simp) with h33 | h33
                                  · rcases p30_3 (m.d 1 2) (by simp) with h34 | h34
                                    · linarith only [h0, h34, hlam]
                                    · linarith only [h34, h8, hlam]
                                  · linarith only [h33, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  rcases p30_3 (m.d 0 2) (by simp) with h38 | h38
                                  · rcases p30_3 (m.d 1 2) (by simp) with h39 | h39
                                    · linarith only [h0, h39, hlam]
                                    · linarith only [h39, h9, hlam]
                                  · linarith only [h38, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  rcases p30_3 (m.d 0 2) (by simp) with h43 | h43
                                  · rcases p30_3 (m.d 1 2) (by simp) with h44 | h44
                                    · linarith only [h0, h44, hlam]
                                    · linarith only [h10, h44, hlam]
                                  · linarith only [h43, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, h26, h28, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, h26, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h2, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h8, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h24, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h26, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h3, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h9, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, h26, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h4, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h10, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p30_1, u3ehi2]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [h28, hlam, p30_0]
                                · have p30_0 := h30c.1
                                  have p30_1 := h30c.2.1
                                  have p30_2 := h30c.2.2.1
                                  have p30_3 := h30c.2.2.2
                                  linarith only [hlam, p30_0]
                              · linarith only [h0, h28, h29, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h11, h2, h23, h24, h28, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                        · linarith only [h21, h70, h8, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h0, h11, h2, h23, h5, h7, h72, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h0, h11, h23, h3, h74, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h11, h23, h76, h8, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h0, h11, h2, h5, h7, h76, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h10, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h3, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
              · rcases m.htr 1 2 5 (by decide) (by decide) with h82 | h82
                · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                        · linarith only [h0, h2, h8, h81, h86, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h8, h81, h83, h86, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                        · linarith only [h0, h2, h8, h81, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h8, h83, h85, h89, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h2, h6, h83, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h8, h81, h83, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h81, h82, h96, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h2, h8, h81, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h8, h81, h94, h98, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h6, h94, h95, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h8, h81, h94, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                          · linarith only [h0, h103, h107, h108, h2, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h103, h107, h108, h2, h6, h81, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h103, h104, h105, h107, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h103, h106, h81, hlam]
                    · linarith only [h0, h104, h105, h2, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                    · linarith only [h104, h114, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h103, h114, h8, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h122 | h122
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                              · rcases h2bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  rcases p124_3 (m.d 0 2) (by simp) with h126 | h126
                                  · rcases p124_3 (m.d 1 2) (by simp) with h127 | h127
                                    · linarith only [h0, h127, hlam]
                                    · rcases p124_3 (m.d 2 3) (by simp) with h129 | h129
                                      · linarith only [h129, h2, hlam]
                                      · linarith only [h129, h8, hlam]
                                  · linarith only [h0, h126, hlam]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h0, h117, h123, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1, u3ehi4]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  rcases p124_3 (m.d 0 2) (by simp) with h134 | h134
                                  · rcases p124_3 (m.d 1 2) (by simp) with h135 | h135
                                    · linarith only [h0, h135, hlam]
                                    · rcases p124_3 (m.d 2 3) (by simp) with h137 | h137
                                      · linarith only [h137, h2, hlam]
                                      · linarith only [h120, h137, hlam]
                                  · linarith only [h134, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  rcases p124_3 (m.d 0 2) (by simp) with h141 | h141
                                  · rcases p124_3 (m.d 1 2) (by simp) with h142 | h142
                                    · linarith only [h0, h142, hlam]
                                    · rcases p124_3 (m.d 2 3) (by simp) with h144 | h144
                                      · linarith only [h144, h2, hlam]
                                      · linarith only [h121, h144, hlam]
                                  · linarith only [h141, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h0, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h8, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h81, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h103, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h2, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  rcases p124_3 (m.d 0 2) (by simp) with h154 | h154
                                  · rcases p124_3 (m.d 1 2) (by simp) with h155 | h155
                                    · linarith only [h155, hlam, p124_0]
                                    · rcases p124_3 (m.d 2 3) (by simp) with h157 | h157
                                      · rcases p124_3 (m.d 2 4) (by simp) with h158 | h158
                                        · linarith only [h120, h158, hlam]
                                        · linarith only [h158, h81, hlam]
                                      · linarith only [h157, hlam, p124_0]
                                  · linarith only [h0, h154, hlam]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h103, h122, hc12, hc23, hlam, hphi, p124_1]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h0, h103, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p124_1]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h3, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  rcases p124_3 (m.d 0 2) (by simp) with h167 | h167
                                  · rcases p124_3 (m.d 1 2) (by simp) with h168 | h168
                                    · linarith only [h168, hlam, p124_0]
                                    · rcases p124_3 (m.d 2 3) (by simp) with h170 | h170
                                      · rcases p124_3 (m.d 2 4) (by simp) with h171 | h171
                                        · rcases p124_3 (m.d 2 5) (by simp) with h172 | h172
                                          · linarith only [h122, h172, hlam]
                                          · linarith only [h103, h172, hlam]
                                        · linarith only [h171, hlam, p124_0]
                                      · linarith only [h170, h8, hlam]
                                  · linarith only [h0, h167, hlam]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h120, hlam, p124_1]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h0, h103, h118, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p124_1, u3ehi4]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h4, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  rcases p124_3 (m.d 0 2) (by simp) with h182 | h182
                                  · rcases p124_3 (m.d 1 2) (by simp) with h183 | h183
                                    · linarith only [h183, hlam, p124_0]
                                    · rcases p124_3 (m.d 2 3) (by simp) with h185 | h185
                                      · rcases p124_3 (m.d 2 4) (by simp) with h186 | h186
                                        · rcases p124_3 (m.d 2 5) (by simp) with h187 | h187
                                          · rcases h3bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h0, h117, h123, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h0, h117, h123, h2, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              rcases p188_3 (m.d 0 3) (by simp) with h192 | h192
                                              · rcases p188_3 (m.d 1 3) (by simp) with h193 | h193
                                                · linarith only [h1, h193, hlam]
                                                · linarith only [h117, h193, hlam]
                                              · linarith only [h192, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              rcases p188_3 (m.d 0 3) (by simp) with h197 | h197
                                              · rcases p188_3 (m.d 1 3) (by simp) with h198 | h198
                                                · linarith only [h1, h198, hlam]
                                                · linarith only [h118, h198, hlam]
                                              · linarith only [h197, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h1, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h8, hlam, p188_1]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h1, h123, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h2, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi1]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h0, h123, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h5, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h117, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h120, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h117, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h6, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h118, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h121, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [h123, hlam, p188_0]
                                            · have p188_0 := h188c.1
                                              have p188_1 := h188c.2.1
                                              have p188_2 := h188c.2.2.1
                                              have p188_3 := h188c.2.2.2
                                              linarith only [hlam, p188_0]
                                          · linarith only [h187, hlam, p124_0]
                                        · linarith only [h186, h81, hlam]
                                      · linarith only [h185, h8, hlam]
                                  · linarith only [h0, h182, hlam]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h121, hlam, p124_1]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [h122, hlam, p124_0]
                                · have p124_0 := h124c.1
                                  have p124_1 := h124c.2.1
                                  have p124_2 := h124c.2.2.1
                                  have p124_3 := h124c.2.2.2
                                  linarith only [hlam, p124_0]
                              · linarith only [h0, h117, h119, h123, h2, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h119, h122, h81, hlam]
                          · linarith only [h0, h117, h121, h2, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h117, h120, h8, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h235 | h235
                            · linarith only [h0, h117, h119, h235, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h237 | h237
                              · linarith only [h117, h235, h237, h81, hlam]
                              · rcases h2bigk with h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c | h239c
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h2, h235, h5, h7, h81, hlam, p239_2]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, h118, h237, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p239_1, u3ehi3]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  rcases p239_3 (m.d 0 2) (by simp) with h243 | h243
                                  · rcases p239_3 (m.d 1 2) (by simp) with h244 | h244
                                    · linarith only [h0, h244, hlam]
                                    · rcases p239_3 (m.d 2 3) (by simp) with h246 | h246
                                      · linarith only [h2, h246, hlam]
                                      · linarith only [h233, h246, hlam]
                                  · linarith only [h243, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  rcases p239_3 (m.d 0 2) (by simp) with h250 | h250
                                  · rcases p239_3 (m.d 1 2) (by simp) with h251 | h251
                                    · linarith only [h0, h251, hlam]
                                    · rcases p239_3 (m.d 2 3) (by simp) with h253 | h253
                                      · linarith only [h2, h253, hlam]
                                      · linarith only [h234, h253, hlam]
                                  · linarith only [h250, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h8, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h81, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h103, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h2, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  rcases p239_3 (m.d 0 2) (by simp) with h263 | h263
                                  · rcases p239_3 (m.d 1 2) (by simp) with h264 | h264
                                    · linarith only [h264, hlam, p239_0]
                                    · rcases p239_3 (m.d 2 3) (by simp) with h266 | h266
                                      · rcases p239_3 (m.d 2 4) (by simp) with h267 | h267
                                        · linarith only [h233, h267, hlam]
                                        · linarith only [h267, h81, hlam]
                                      · linarith only [h266, hlam, p239_0]
                                  · linarith only [h0, h263, hlam]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h81, hc12, hc23, hlam, hphi, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, h103, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h3, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h0, h2, h235, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h233, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h235, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h4, hlam, p239_0]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  rcases p239_3 (m.d 0 2) (by simp) with h281 | h281
                                  · rcases p239_3 (m.d 1 2) (by simp) with h282 | h282
                                    · linarith only [h282, hlam, p239_0]
                                    · rcases p239_3 (m.d 2 3) (by simp) with h284 | h284
                                      · rcases p239_3 (m.d 2 4) (by simp) with h285 | h285
                                        · linarith only [h235, h285, hlam]
                                        · linarith only [h285, h81, hlam]
                                      · linarith only [h284, h8, hlam]
                                  · linarith only [h0, h281, hlam]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h234, hlam, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [h81, hc12, hc25, hlam, hphi, p239_1]
                                · have p239_0 := h239c.1
                                  have p239_1 := h239c.2.1
                                  have p239_2 := h239c.2.2.1
                                  have p239_3 := h239c.2.2.2
                                  linarith only [hlam, p239_0]
                          · linarith only [h1, h118, h234, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h117, h233, h8, hlam]
                    · linarith only [h117, h118, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                    · linarith only [h0, h117, h2, h296, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                        · linarith only [h0, h117, h2, h299, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                          · linarith only [h296, h299, h301, h5, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                              · rcases h2bigk with h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h2, h301, h304, h5, h8, hlam, p305_2]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  rcases p305_3 (m.d 0 2) (by simp) with h308 | h308
                                  · rcases p305_3 (m.d 1 2) (by simp) with h309 | h309
                                    · linarith only [h0, h309, hlam]
                                    · rcases p305_3 (m.d 2 3) (by simp) with h311 | h311
                                      · linarith only [h311, hlam, p305_0]
                                      · rcases p305_3 (m.d 2 4) (by simp) with h313 | h313
                                        · linarith only [h3, h313, hlam]
                                        · linarith only [h299, h313, hlam]
                                  · linarith only [h308, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  rcases p305_3 (m.d 0 2) (by simp) with h317 | h317
                                  · rcases p305_3 (m.d 1 2) (by simp) with h318 | h318
                                    · linarith only [h0, h318, hlam]
                                    · rcases p305_3 (m.d 2 3) (by simp) with h320 | h320
                                      · linarith only [h2, h320, hlam]
                                      · rcases p305_3 (m.d 2 4) (by simp) with h322 | h322
                                        · linarith only [h322, hlam, p305_0]
                                        · rcases p305_3 (m.d 2 5) (by simp) with h324 | h324
                                          · linarith only [h324, h4, hlam]
                                          · rcases h3bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              rcases p326_3 (m.d 0 3) (by simp) with h328 | h328
                                              · rcases p326_3 (m.d 1 3) (by simp) with h329 | h329
                                                · linarith only [h1, h329, hlam]
                                                · rcases p326_3 (m.d 2 3) (by simp) with h331 | h331
                                                  · linarith only [h2, h331, hlam]
                                                  · linarith only [h331, h8, hlam]
                                              · linarith only [h1, h328, hlam]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              rcases p326_3 (m.d 0 3) (by simp) with h335 | h335
                                              · rcases p326_3 (m.d 1 3) (by simp) with h336 | h336
                                                · linarith only [h1, h336, hlam]
                                                · rcases p326_3 (m.d 2 3) (by simp) with h338 | h338
                                                  · linarith only [h2, h338, hlam]
                                                  · rcases p326_3 (m.d 3 4) (by simp) with h340 | h340
                                                    · linarith only [h340, h5, hlam]
                                                    · linarith only [h299, h340, hlam]
                                              · linarith only [h2, h335, hlam]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h0, h2, h301, h304, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p326_1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h0, h2, h301, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p326_1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h1, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h8, hlam, p326_1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h117, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h296, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h2, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h301, h6, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p326_1, u3ehi1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h299, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h301, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h5, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p326_1, u3ehi1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p326_1, u3ehi2]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p326_1, u3ehi4]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h6, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [hc35, hlam, hphi, p326_1, u3ehi1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h0, h2, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p326_1]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [h304, hlam, p326_0]
                                            · have p326_0 := h326c.1
                                              have p326_1 := h326c.2.1
                                              have p326_2 := h326c.2.2.1
                                              have p326_3 := h326c.2.2.2
                                              linarith only [hlam, p326_0]
                                  · linarith only [h317, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  rcases p305_3 (m.d 0 2) (by simp) with h367 | h367
                                  · rcases p305_3 (m.d 1 2) (by simp) with h368 | h368
                                    · linarith only [h0, h368, hlam]
                                    · rcases p305_3 (m.d 2 3) (by simp) with h370 | h370
                                      · linarith only [h2, h370, hlam]
                                      · rcases p305_3 (m.d 2 4) (by simp) with h372 | h372
                                        · linarith only [h3, h372, hlam]
                                        · linarith only [h303, h372, hlam]
                                  · linarith only [h367, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h0, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h8, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h81, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h103, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h2, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h0, h2, h299, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h299, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h301, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h3, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  rcases p305_3 (m.d 0 2) (by simp) with h387 | h387
                                  · rcases p305_3 (m.d 1 2) (by simp) with h388 | h388
                                    · linarith only [h388, hlam, p305_0]
                                    · rcases p305_3 (m.d 2 3) (by simp) with h390 | h390
                                      · linarith only [h299, h390, hlam]
                                      · linarith only [h390, h8, hlam]
                                  · linarith only [h0, h387, hlam]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p305_1, u3ehi2]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h0, h103, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h4, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  rcases p305_3 (m.d 0 2) (by simp) with h398 | h398
                                  · rcases p305_3 (m.d 1 2) (by simp) with h399 | h399
                                    · linarith only [h399, hlam, p305_0]
                                    · rcases p305_3 (m.d 2 3) (by simp) with h401 | h401
                                      · linarith only [h301, h401, hlam]
                                      · linarith only [h401, h8, hlam]
                                  · linarith only [h0, h398, hlam]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h8, hc12, hc25, hlam, hphi, p305_1]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [h303, hlam, p305_0]
                                · have p305_0 := h305c.1
                                  have p305_1 := h305c.2.1
                                  have p305_2 := h305c.2.2.1
                                  have p305_3 := h305c.2.2.2
                                  linarith only [hlam, p305_0]
                              · linarith only [h298, h299, h304, h81, hlam]
                            · linarith only [h298, h303, h81, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                        · linarith only [h0, h117, h2, h410, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h412 | h412
                          · linarith only [h410, h412, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                            · linarith only [h0, h117, h2, h298, h410, h414, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                              · linarith only [h0, h2, h414, h416, h5, h81, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h0, h117, h2, h416, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
            · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
              · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
                · rcases m.htr 1 3 4 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h424 | h424
                      · linarith only [h424, h7, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h426 | h426
                        · linarith only [h0, h419, h426, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h422, h426, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h422, h423, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h422, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h0, h4, h419, h421, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h3, h419, h420, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h433 | h433
              · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
                · rcases m.htr 1 3 4 (by decide) (by decide) with h435 | h435
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h436 | h436
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h437 | h437
                      · linarith only [h433, h437, h7, hc12, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
                        · linarith only [h0, h2, h419, h433, h439, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h419, h433, h435, h439, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h2, h435, h436, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h435, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                      · linarith only [h433, h446, h7, hc12, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                        · linarith only [h0, h4, h433, h434, h448, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h444, h448, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2, h444, h445, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h444, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h455 | h455
                    · linarith only [h3, h433, h453, h455, h7, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h454, h455, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h454, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h460 | h460
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
                      · linarith only [h461, h7, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h464 | h464
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h465 | h465
                            · linarith only [h3, h465, h7, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                              · linarith only [h459, h467, h7, hc13, hlam, hphi, ht01, u0ehi3]
                              · rcases h2bigk with h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  rcases p469_3 (m.d 0 2) (by simp) with h471 | h471
                                  · rcases p469_3 (m.d 1 2) (by simp) with h472 | h472
                                    · linarith only [h0, h472, hlam]
                                    · rcases p469_3 (m.d 2 3) (by simp) with h474 | h474
                                      · linarith only [h2, h474, hlam]
                                      · linarith only [h419, h474, hlam]
                                  · linarith only [h0, h471, hlam]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h0, h419, h460, h467, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p469_1, u3ehi3]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  rcases p469_3 (m.d 0 2) (by simp) with h479 | h479
                                  · rcases p469_3 (m.d 1 2) (by simp) with h480 | h480
                                    · linarith only [h0, h480, hlam]
                                    · rcases p469_3 (m.d 2 3) (by simp) with h482 | h482
                                      · linarith only [h2, h482, hlam]
                                      · linarith only [h463, h482, hlam]
                                  · linarith only [h479, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  rcases p469_3 (m.d 0 2) (by simp) with h486 | h486
                                  · rcases p469_3 (m.d 1 2) (by simp) with h487 | h487
                                    · linarith only [h0, h487, hlam]
                                    · rcases p469_3 (m.d 2 3) (by simp) with h489 | h489
                                      · linarith only [h2, h489, hlam]
                                      · linarith only [h464, h489, hlam]
                                  · linarith only [h486, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h0, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h419, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h433, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h453, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h2, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  rcases p469_3 (m.d 0 2) (by simp) with h499 | h499
                                  · rcases p469_3 (m.d 1 2) (by simp) with h500 | h500
                                    · linarith only [h500, hlam, p469_0]
                                    · rcases p469_3 (m.d 2 3) (by simp) with h502 | h502
                                      · rcases p469_3 (m.d 2 4) (by simp) with h503 | h503
                                        · linarith only [h463, h503, hlam]
                                        · linarith only [h433, h503, hlam]
                                      · linarith only [h502, hlam, p469_0]
                                  · linarith only [h0, h499, hlam]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h433, hc12, hc23, hlam, hphi, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h0, h2, h433, h465, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h3, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h3, h7, hc12, hc45, hlam, hphi, ht23, ht34, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h463, hlam, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h465, hlam, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h4, hlam, p469_0]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  rcases p469_3 (m.d 0 2) (by simp) with h517 | h517
                                  · rcases p469_3 (m.d 1 2) (by simp) with h518 | h518
                                    · linarith only [h518, hlam, p469_0]
                                    · rcases p469_3 (m.d 2 3) (by simp) with h520 | h520
                                      · rcases p469_3 (m.d 2 4) (by simp) with h521 | h521
                                        · linarith only [h465, h521, hlam]
                                        · linarith only [h433, h521, hlam]
                                      · linarith only [h419, h520, hlam]
                                  · linarith only [h0, h517, hlam]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h464, hlam, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [h433, hc12, hc25, hlam, hphi, p469_1]
                                · have p469_0 := h469c.1
                                  have p469_1 := h469c.2.1
                                  have p469_2 := h469c.2.2.1
                                  have p469_3 := h469c.2.2.2
                                  linarith only [hlam, p469_0]
                          · linarith only [h1, h460, h464, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h3, h419, h433, h459, h463, h7, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h459, h460, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h459, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
        · linarith only [h5, h534, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
          · rcases m.htr 1 2 3 (by decide) (by decide) with h537 | h537
            · rcases m.htr 1 2 4 (by decide) (by decide) with h538 | h538
              · rcases m.htr 1 2 5 (by decide) (by decide) with h539 | h539
                · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                  · linarith only [h5, h540, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                    · linarith only [h1, h534, h542, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                        · linarith only [h5, h545, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h547 | h547
                          · linarith only [h534, h537, h547, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h549 | h549
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h550 | h550
                              · rcases h2bigk with h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h538, h547, h549, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  rcases p551_3 (m.d 0 2) (by simp) with h554 | h554
                                  · rcases p551_3 (m.d 1 2) (by simp) with h555 | h555
                                    · linarith only [h0, h555, hlam]
                                    · linarith only [h537, h555, hlam]
                                  · linarith only [h554, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  rcases p551_3 (m.d 0 2) (by simp) with h559 | h559
                                  · rcases p551_3 (m.d 1 2) (by simp) with h560 | h560
                                    · linarith only [h0, h560, hlam]
                                    · linarith only [h538, h560, hlam]
                                  · linarith only [h559, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  rcases p551_3 (m.d 0 2) (by simp) with h564 | h564
                                  · rcases p551_3 (m.d 1 2) (by simp) with h565 | h565
                                    · linarith only [h0, h565, hlam]
                                    · linarith only [h539, h565, hlam]
                                  · linarith only [h564, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, h547, h549, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, h547, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h2, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h537, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h545, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h547, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h3, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h538, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, h538, h547, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h4, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h539, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u3ehi2]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [h549, hlam, p551_0]
                                · have p551_0 := h551c.1
                                  have p551_1 := h551c.2.1
                                  have p551_2 := h551c.2.2.1
                                  have p551_3 := h551c.2.2.2
                                  linarith only [hlam, p551_0]
                              · linarith only [h0, h538, h549, h550, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h538, h544, h545, h549, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h5, h536, h540, h544, hc34, hlam, hphi, u3ehi1]
                · linarith only [h0, h4, h537, h539, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h3, h537, h538, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h594 | h594
              · rcases m.htr 1 2 5 (by decide) (by decide) with h595 | h595
                · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                  · linarith only [h1, h5, h596, hc01, hlam, hphi, u0ehi3]
                  · linarith only [h2, h534, h537, h594, h596, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h599 | h599
                  · linarith only [h2, h5, h537, h594, h599, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h2, h534, h537, h594, h599, hc35, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                  · linarith only [h2, h5, h537, h602, h603, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h605 | h605
                    · linarith only [h2, h534, h537, h605, hlam]
                    · linarith only [h2, h5, h537, h602, h605, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                  · linarith only [h5, h608, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h610 | h610
                    · linarith only [h2, h534, h537, h610, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                        · linarith only [h2, h5, h613, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                          · linarith only [h2, h534, h615, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                              · rcases h2bigk with h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c | h619c
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  rcases p619_3 (m.d 0 2) (by simp) with h621 | h621
                                  · rcases p619_3 (m.d 1 2) (by simp) with h622 | h622
                                    · linarith only [h0, h622, hlam]
                                    · rcases p619_3 (m.d 2 3) (by simp) with h624 | h624
                                      · linarith only [h2, h624, hlam]
                                      · linarith only [h537, h624, hlam]
                                  · linarith only [h0, h621, hlam]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  rcases p619_3 (m.d 0 2) (by simp) with h628 | h628
                                  · rcases p619_3 (m.d 1 2) (by simp) with h629 | h629
                                    · linarith only [h0, h629, hlam]
                                    · rcases p619_3 (m.d 2 3) (by simp) with h631 | h631
                                      · linarith only [h631, hlam, p619_0]
                                      · rcases p619_3 (m.d 2 4) (by simp) with h633 | h633
                                        · linarith only [h3, h633, hlam]
                                        · linarith only [h613, h633, hlam]
                                  · linarith only [h628, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  rcases p619_3 (m.d 0 2) (by simp) with h637 | h637
                                  · rcases p619_3 (m.d 1 2) (by simp) with h638 | h638
                                    · linarith only [h0, h638, hlam]
                                    · rcases p619_3 (m.d 2 3) (by simp) with h640 | h640
                                      · linarith only [h2, h640, hlam]
                                      · rcases p619_3 (m.d 2 4) (by simp) with h642 | h642
                                        · linarith only [h642, hlam, p619_0]
                                        · rcases p619_3 (m.d 2 5) (by simp) with h644 | h644
                                          · linarith only [h4, h644, hlam]
                                          · rcases h3bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h534, h618, hc34, hlam, hphi, p646_1, u3ehi1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h534, h537, h618, hc12, hc34, hlam, hphi, ht23, p646_1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h5, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h534, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h1, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h537, hlam, p646_1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h608, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h610, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h2, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1, u3ehi1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h613, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h615, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hc34, hlam, hphi, p646_1, u3ehi0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hc34, hlam, hphi, p646_1, u3ehi1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h537, hc12, hc34, hlam, hphi, ht23, p646_1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hc34, hlam, hphi, p646_1, u3ehi4]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p646_1, u0ehi2]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hc35, hlam, hphi, p646_1, u3ehi1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h537, hc12, hc35, hlam, hphi, ht23, p646_1]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [h618, hlam, p646_0]
                                            · have p646_0 := h646c.1
                                              have p646_1 := h646c.2.1
                                              have p646_2 := h646c.2.2.1
                                              have p646_3 := h646c.2.2.2
                                              linarith only [hlam, p646_0]
                                  · linarith only [h637, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  rcases p619_3 (m.d 0 2) (by simp) with h673 | h673
                                  · rcases p619_3 (m.d 1 2) (by simp) with h674 | h674
                                    · linarith only [h0, h674, hlam]
                                    · rcases p619_3 (m.d 2 3) (by simp) with h676 | h676
                                      · linarith only [h2, h676, hlam]
                                      · rcases p619_3 (m.d 2 4) (by simp) with h678 | h678
                                        · linarith only [h3, h678, hlam]
                                        · linarith only [h617, h678, hlam]
                                  · linarith only [h673, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h0, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h537, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h594, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h602, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h2, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p619_1]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h613, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h615, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h3, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  rcases p619_3 (m.d 0 2) (by simp) with h693 | h693
                                  · rcases p619_3 (m.d 1 2) (by simp) with h694 | h694
                                    · linarith only [h694, hlam, p619_0]
                                    · rcases p619_3 (m.d 2 3) (by simp) with h696 | h696
                                      · linarith only [h613, h696, hlam]
                                      · linarith only [h537, h696, hlam]
                                  · linarith only [h0, h693, hlam]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p619_1, u3ehi2]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h0, h3, h602, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p619_1]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h4, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  rcases p619_3 (m.d 0 2) (by simp) with h704 | h704
                                  · rcases p619_3 (m.d 1 2) (by simp) with h705 | h705
                                    · linarith only [h705, hlam, p619_0]
                                    · rcases p619_3 (m.d 2 3) (by simp) with h707 | h707
                                      · linarith only [h615, h707, hlam]
                                      · linarith only [h537, h707, hlam]
                                  · linarith only [h0, h704, hlam]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h537, hc12, hc25, hlam, hphi, p619_1]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [h617, hlam, p619_0]
                                · have p619_0 := h619c.1
                                  have p619_1 := h619c.2.1
                                  have p619_2 := h619c.2.2.1
                                  have p619_3 := h619c.2.2.2
                                  linarith only [hlam, p619_0]
                              · linarith only [h0, h3, h594, h612, h618, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h594, h612, h617, hlam]
                      · linarith only [h5, h536, h608, h612, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h717 | h717
            · rcases m.htr 1 2 4 (by decide) (by decide) with h718 | h718
              · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                · rcases m.htr 1 3 4 (by decide) (by decide) with h720 | h720
                  · linarith only [h1, h5, h536, h720, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h722 | h722
                    · linarith only [h1, h5, h536, h722, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h724 | h724
                      · linarith only [h5, h536, h724, hc14, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h726 | h726
                        · linarith only [h5, h717, h726, hc12, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h728 | h728
                          · linarith only [h1, h534, h717, h728, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h730 | h730
                            · linarith only [h0, h718, h724, h730, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h732 | h732
                              · linarith only [h5, h536, h732, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                              · linarith only [h5, h732, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                · linarith only [h0, h4, h717, h719, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h3, h717, h718, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h737 | h737
              · linarith only [h2, h5, h536, h717, h737, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h739 | h739
                · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
                  · linarith only [h2, h5, h536, h717, h740, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h742 | h742
                    · linarith only [h2, h534, h717, h742, hlam]
                    · linarith only [h2, h5, h536, h717, h739, h742, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h745 | h745
                  · linarith only [h5, h745, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h747 | h747
                    · linarith only [h2, h534, h717, h747, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
                      · linarith only [h5, h536, h749, hc14, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                        · linarith only [h2, h5, h751, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                          · linarith only [h2, h534, h753, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h755 | h755
                            · linarith only [h3, h536, h755, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h757 | h757
                              · linarith only [h5, h536, h757, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                              · linarith only [h5, h757, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h760 | h760
      · rcases m.htr 0 3 5 (by decide) (by decide) with h761 | h761
        · linarith only [h2, h4, h761, hlam]
        · linarith only [h760, h761, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h764 | h764
        · linarith only [h760, h764, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h766 | h766
          · linarith only [h3, h4, h766, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
            · rcases m.htr 1 2 4 (by decide) (by decide) with h769 | h769
              · rcases m.htr 1 2 5 (by decide) (by decide) with h770 | h770
                · linarith only [h0, h4, h770, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h772 | h772
                  · linarith only [h1, h760, h766, h772, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h774 | h774
                    · linarith only [h1, h764, h774, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h776 | h776
                      · linarith only [h760, h766, h776, hc14, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                        · linarith only [h0, h4, h760, h768, h778, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
                          · linarith only [h0, h4, h764, h769, h778, h780, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                          · linarith only [h0, h4, h769, h778, h780, hc35, hlam, hphi, u3ehi2]
              · linarith only [h3, h4, h769, hc12, hc25, hlam, hphi]
            · linarith only [h2, h4, h768, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h785 | h785
    · rcases m.htr 0 3 4 (by decide) (by decide) with h786 | h786
      · linarith only [h2, h3, h786, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h788 | h788
        · linarith only [h786, h788, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h790 | h790
          · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
            · rcases m.htr 1 2 4 (by decide) (by decide) with h792 | h792
              · linarith only [h0, h3, h792, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
                  · linarith only [h786, h795, hc13, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h797 | h797
                    · linarith only [h1, h788, h797, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h800 | h800
                        · linarith only [h0, h3, h786, h791, h800, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                        · linarith only [h0, h3, h791, h800, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h791, h792, h799, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h785, h791, h794, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h2, h3, h791, hc12, hc24, hlam, hphi]
          · linarith only [h2, h3, h790, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h807 | h807
      · linarith only [h2, h3, h807, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h809 | h809
        · linarith only [h807, h809, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h811 | h811
          · rcases m.htr 1 2 3 (by decide) (by decide) with h812 | h812
            · rcases m.htr 1 2 4 (by decide) (by decide) with h813 | h813
              · linarith only [h3, h813, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h815 | h815
                · linarith only [h0, h785, h815, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h817 | h817
                  · linarith only [h1, h807, h817, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h819 | h819
                    · linarith only [h1, h809, h819, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h821 | h821
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h822 | h822
                        · linarith only [h0, h3, h807, h812, h822, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2, h3, h822, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h812, h813, h821, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h2, h3, h812, hc12, hc24, hlam, hphi]
          · linarith only [h2, h3, h811, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
