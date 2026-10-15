import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_R_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
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
                              · linarith only [h0, h70, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                                · linarith only [h21, h72, h8, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                                  · linarith only [h0, h11, h23, h3, h74, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                                    · linarith only [h0, h11, h2, h23, h5, h76, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
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
                              · linarith only [h8, h81, h83, h85, h89, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h2, h6, h83, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h8, h81, h83, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h81, h82, h96, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                              · linarith only [h0, h4, h81, h82, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h8, h95, h98, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h0, h2, h6, h94, h95, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h8, h81, h94, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h105 | h105
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h107 | h107
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h108 | h108
                                · linarith only [h0, h103, h107, h108, h2, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h104, h108, h8, hc35, hlam, hphi, u3ehi3]
                              · linarith only [h104, h107, h8, hlam]
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
                                        linarith only [h0, h117, h123, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p124_1]
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
                                                · rcases h5bigk with h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c | h188c
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [hlam, p188_0]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    rcases p188_3 (m.d 0 5) (by simp) with h190 | h190
                                                    · rcases p188_3 (m.d 1 5) (by simp) with h191 | h191
                                                      · linarith only [h1, h191, hlam]
                                                      · rcases p188_3 (m.d 2 5) (by simp) with h193 | h193
                                                        · linarith only [h193, h4, hlam]
                                                        · linarith only [h103, h193, hlam]
                                                    · linarith only [h1, h190, hlam]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h0, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p124_1, p188_1]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    rcases p188_3 (m.d 0 5) (by simp) with h198 | h198
                                                    · rcases p188_3 (m.d 1 5) (by simp) with h199 | h199
                                                      · linarith only [h1, h199, hlam]
                                                      · linarith only [h118, h199, hlam]
                                                    · linarith only [h198, h6, hlam]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    rcases p188_3 (m.d 0 5) (by simp) with h203 | h203
                                                    · rcases p188_3 (m.d 1 5) (by simp) with h204 | h204
                                                      · linarith only [h1, h204, hlam]
                                                      · linarith only [h119, h204, hlam]
                                                    · linarith only [h203, h7, hlam]
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
                                                    linarith only [h103, hlam, p188_0]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    rcases p188_3 (m.d 0 5) (by simp) with h212 | h212
                                                    · rcases p188_3 (m.d 1 5) (by simp) with h213 | h213
                                                      · rcases p188_3 (m.d 2 5) (by simp) with h214 | h214
                                                        · rcases p188_3 (m.d 3 5) (by simp) with h215 | h215
                                                          · linarith only [h118, h215, hlam]
                                                          · linarith only [h123, h215, hlam]
                                                        · linarith only [h122, h214, hlam]
                                                      · linarith only [h119, h213, hlam]
                                                    · linarith only [h212, h7, hlam]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h4, hlam, p188_1]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h0, h118, h120, h122, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [hlam, p188_0]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h0, h120, h122, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p188_1, u3ehi4]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    rcases p188_3 (m.d 0 5) (by simp) with h225 | h225
                                                    · rcases p188_3 (m.d 1 5) (by simp) with h226 | h226
                                                      · linarith only [h103, h226, hlam]
                                                      · linarith only [h119, h226, hlam]
                                                    · linarith only [h225, h7, hlam]
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
                                                    linarith only [hlam, p188_0]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h0, h117, h123, h2, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p188_1]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h7, hlam, p188_0]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h119, hlam, p188_0]
                                                  · have p188_0 := h188c.1
                                                    have p188_1 := h188c.2.1
                                                    have p188_2 := h188c.2.2.1
                                                    have p188_3 := h188c.2.2.2
                                                    linarith only [h122, hlam, p188_0]
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
                                  · linarith only [h0, h117, h119, h122, h2, h8, h81, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h118, h121, h8, hlam]
                              · linarith only [h118, h120, h8, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h252 | h252
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h253 | h253
                                  · linarith only [h0, h117, h119, h253, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h255 | h255
                                    · linarith only [h117, h253, h255, h81, hlam]
                                    · rcases h2bigk with h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c | h257c
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h2, h253, h5, h7, h81, hlam, p257_2]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h118, h255, h8, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p257_1, u3ehi3]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        rcases p257_3 (m.d 0 2) (by simp) with h261 | h261
                                        · rcases p257_3 (m.d 1 2) (by simp) with h262 | h262
                                          · linarith only [h0, h262, hlam]
                                          · rcases p257_3 (m.d 2 3) (by simp) with h264 | h264
                                            · linarith only [h2, h264, hlam]
                                            · linarith only [h251, h264, hlam]
                                        · linarith only [h261, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        rcases p257_3 (m.d 0 2) (by simp) with h268 | h268
                                        · rcases p257_3 (m.d 1 2) (by simp) with h269 | h269
                                          · linarith only [h0, h269, hlam]
                                          · rcases p257_3 (m.d 2 3) (by simp) with h271 | h271
                                            · linarith only [h2, h271, hlam]
                                            · linarith only [h252, h271, hlam]
                                        · linarith only [h268, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h0, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h8, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h81, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h103, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h2, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        rcases p257_3 (m.d 0 2) (by simp) with h281 | h281
                                        · rcases p257_3 (m.d 1 2) (by simp) with h282 | h282
                                          · linarith only [h282, hlam, p257_0]
                                          · rcases p257_3 (m.d 2 3) (by simp) with h284 | h284
                                            · rcases p257_3 (m.d 2 4) (by simp) with h285 | h285
                                              · linarith only [h251, h285, hlam]
                                              · linarith only [h285, h81, hlam]
                                            · linarith only [h284, hlam, p257_0]
                                        · linarith only [h0, h281, hlam]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h81, hc12, hc23, hlam, hphi, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h0, h103, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h3, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h253, h5, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h251, hlam, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h253, hlam, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h4, hlam, p257_0]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        rcases p257_3 (m.d 0 2) (by simp) with h299 | h299
                                        · rcases p257_3 (m.d 1 2) (by simp) with h300 | h300
                                          · linarith only [h300, hlam, p257_0]
                                          · rcases p257_3 (m.d 2 3) (by simp) with h302 | h302
                                            · rcases p257_3 (m.d 2 4) (by simp) with h303 | h303
                                              · linarith only [h253, h303, hlam]
                                              · linarith only [h303, h81, hlam]
                                            · linarith only [h302, h8, hlam]
                                        · linarith only [h0, h299, hlam]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h252, hlam, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [h81, hc12, hc25, hlam, hphi, p257_1]
                                      · have p257_0 := h257c.1
                                        have p257_1 := h257c.2.1
                                        have p257_2 := h257c.2.2.1
                                        have p257_3 := h257c.2.2.2
                                        linarith only [hlam, p257_0]
                                · linarith only [h118, h252, h8, hlam]
                              · linarith only [h118, h251, h8, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h117, h118, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h314 | h314
                          · linarith only [h117, h314, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h316 | h316
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                              · linarith only [h0, h117, h2, h317, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                                · linarith only [h0, h2, h314, h319, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
                                    · rcases h2bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h2, h319, h322, h5, h8, hlam, p323_2]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        rcases p323_3 (m.d 0 2) (by simp) with h326 | h326
                                        · rcases p323_3 (m.d 1 2) (by simp) with h327 | h327
                                          · linarith only [h0, h327, hlam]
                                          · rcases p323_3 (m.d 2 3) (by simp) with h329 | h329
                                            · linarith only [h329, hlam, p323_0]
                                            · rcases p323_3 (m.d 2 4) (by simp) with h331 | h331
                                              · linarith only [h3, h331, hlam]
                                              · linarith only [h317, h331, hlam]
                                        · linarith only [h326, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        rcases p323_3 (m.d 0 2) (by simp) with h335 | h335
                                        · rcases p323_3 (m.d 1 2) (by simp) with h336 | h336
                                          · linarith only [h0, h336, hlam]
                                          · rcases p323_3 (m.d 2 3) (by simp) with h338 | h338
                                            · linarith only [h2, h338, hlam]
                                            · rcases p323_3 (m.d 2 4) (by simp) with h340 | h340
                                              · linarith only [h340, hlam, p323_0]
                                              · rcases p323_3 (m.d 2 5) (by simp) with h342 | h342
                                                · linarith only [h342, h4, hlam]
                                                · rcases h5bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    rcases p344_3 (m.d 0 5) (by simp) with h346 | h346
                                                    · rcases p344_3 (m.d 1 5) (by simp) with h347 | h347
                                                      · linarith only [h1, h347, hlam]
                                                      · rcases p344_3 (m.d 2 5) (by simp) with h349 | h349
                                                        · linarith only [h349, h4, hlam]
                                                        · linarith only [h103, h349, hlam]
                                                    · linarith only [h1, h346, hlam]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    rcases p344_3 (m.d 0 5) (by simp) with h353 | h353
                                                    · rcases p344_3 (m.d 1 5) (by simp) with h354 | h354
                                                      · linarith only [h1, h354, hlam]
                                                      · rcases p344_3 (m.d 2 5) (by simp) with h356 | h356
                                                        · linarith only [h356, h4, hlam]
                                                        · rcases p344_3 (m.d 3 5) (by simp) with h358 | h358
                                                          · linarith only [h358, h6, hlam]
                                                          · linarith only [h319, h358, hlam]
                                                    · linarith only [h353, h4, hlam]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h0, h2, h314, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1, u3ehi1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    rcases p344_3 (m.d 0 5) (by simp) with h363 | h363
                                                    · rcases p344_3 (m.d 1 5) (by simp) with h364 | h364
                                                      · linarith only [h1, h364, hlam]
                                                      · linarith only [h316, h364, hlam]
                                                    · linarith only [h363, h7, hlam]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h1, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h103, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h314, hlam, p344_1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h0, h316, h81, hc01, hc45, hlam, hphi, ht0b, ht5b, p323_1, p344_1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h4, hlam, p344_1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h0, h314, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1, u3ehi1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h319, hlam, p344_1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h0, h321, hc01, hc45, hlam, hphi, ht0b, ht5b, p323_1, p344_1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h6, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h0, h2, h314, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1, u3ehi1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h0, h2, h319, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p344_1]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    rcases p344_3 (m.d 0 5) (by simp) with h382 | h382
                                                    · rcases p344_3 (m.d 1 5) (by simp) with h383 | h383
                                                      · linarith only [h314, h383, hlam]
                                                      · linarith only [h316, h383, hlam]
                                                    · linarith only [h382, h7, hlam]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h7, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h316, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h321, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [h322, hlam, p344_0]
                                                  · have p344_0 := h344c.1
                                                    have p344_1 := h344c.2.1
                                                    have p344_2 := h344c.2.2.1
                                                    have p344_3 := h344c.2.2.2
                                                    linarith only [hlam, p344_0]
                                        · linarith only [h335, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        rcases p323_3 (m.d 0 2) (by simp) with h393 | h393
                                        · rcases p323_3 (m.d 1 2) (by simp) with h394 | h394
                                          · linarith only [h0, h394, hlam]
                                          · rcases p323_3 (m.d 2 3) (by simp) with h396 | h396
                                            · linarith only [h2, h396, hlam]
                                            · rcases p323_3 (m.d 2 4) (by simp) with h398 | h398
                                              · linarith only [h3, h398, hlam]
                                              · linarith only [h321, h398, hlam]
                                        · linarith only [h393, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h0, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h8, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h81, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h103, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h2, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h0, h2, h317, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p323_1]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h317, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h319, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h3, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        rcases p323_3 (m.d 0 2) (by simp) with h413 | h413
                                        · rcases p323_3 (m.d 1 2) (by simp) with h414 | h414
                                          · linarith only [h414, hlam, p323_0]
                                          · rcases p323_3 (m.d 2 3) (by simp) with h416 | h416
                                            · linarith only [h317, h416, hlam]
                                            · linarith only [h416, h8, hlam]
                                        · linarith only [h0, h413, hlam]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p323_1, u3ehi2]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h0, h2, h317, h319, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p323_1]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h4, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        rcases p323_3 (m.d 0 2) (by simp) with h424 | h424
                                        · rcases p323_3 (m.d 1 2) (by simp) with h425 | h425
                                          · linarith only [h425, hlam, p323_0]
                                          · rcases p323_3 (m.d 2 3) (by simp) with h427 | h427
                                            · linarith only [h319, h427, hlam]
                                            · linarith only [h427, h8, hlam]
                                        · linarith only [h0, h424, hlam]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h8, hc12, hc25, hlam, hphi, p323_1]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [h321, hlam, p323_0]
                                      · have p323_0 := h323c.1
                                        have p323_1 := h323c.2.1
                                        have p323_2 := h323c.2.2.1
                                        have p323_3 := h323c.2.2.2
                                        linarith only [hlam, p323_0]
                                    · linarith only [h0, h117, h2, h322, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h316, h321, h81, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h436 | h436
                              · linarith only [h0, h117, h2, h436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                                · linarith only [h436, h438, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h440 | h440
                                  · linarith only [h0, h117, h2, h316, h436, h440, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h442 | h442
                                    · linarith only [h0, h2, h436, h440, h442, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                    · linarith only [h0, h117, h2, h442, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc15, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_13_15_M_LR_L_R_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · linarith only [h2, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · linarith only [h2, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · linarith only [h0, h12, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h15, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · linarith only [h0, h15, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h20, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
              · linarith only [h1, h20, h22, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h1, h24, h28, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases h3bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h22, h24, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u0elo2, u2ehi1]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h2, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            rcases p30_3 (m.d 0 3) (by simp) with h34 | h34
                            · rcases p30_3 (m.d 1 3) (by simp) with h35 | h35
                              · linarith only [h1, h35, hlam]
                              · linarith only [h24, h35, hlam]
                            · linarith only [h34, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            rcases p30_3 (m.d 0 3) (by simp) with h39 | h39
                            · rcases p30_3 (m.d 1 3) (by simp) with h40 | h40
                              · linarith only [h1, h40, hlam]
                              · linarith only [h25, h40, hlam]
                            · linarith only [h39, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h1, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h20, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1, u0elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h1, hc35, hlam, hphi, ht0b, ht5b, p30_1, u0elo0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p30_1, u0ehi7]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h20, hc23, hlam, hphi, p30_1, u2ehi1]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            rcases p30_3 (m.d 0 3) (by simp) with h52 | h52
                            · linarith only [h2, h52, hlam]
                            · linarith only [h18, h52, hlam]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            rcases p30_3 (m.d 0 3) (by simp) with h55 | h55
                            · linarith only [h2, h55, hlam]
                            · linarith only [h19, h55, hlam]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h18, hlam, p30_0]
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
                            linarith only [hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h28, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h19, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h25, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h27, hlam, p30_0]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [h19, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1, u0elo2]
                          · have p30_0 := h30c.1
                            have p30_1 := h30c.2.1
                            have p30_2 := h30c.2.2.1
                            have p30_3 := h30c.2.2.2
                            linarith only [hlam, p30_0]
                      · linarith only [h1, h25, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1, h2, h22, h24, h26, hc34, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                  · linarith only [h1, h19, h22, h24, h25, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · linarith only [h1, h18, h20, h24, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
            · linarith only [h2, h72, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
              · linarith only [h0, h74, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h1, h19, h77, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                      · linarith only [h19, h2, h80, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h1, h2, h74, h76, h80, hc35, hlam, hphi, ht23, u0ehi6, u0elo0, u2ehi1]
                    · linarith only [h1, h2, h76, h79, hlam, hphi, u0ehi6, u0elo0]
                · linarith only [h18, h19, h76, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h85 | h85
          · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
            · linarith only [h2, h86, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
              · linarith only [h1, h86, h88, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                · linarith only [h1, h18, h90, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                    · linarith only [h18, h85, h93, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                    · linarith only [h2, h93, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h18, h85, h86, h92, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
            · linarith only [h0, h97, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
              · linarith only [h0, h99, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                · linarith only [h1, h101, h18, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h1, h103, h2, h85, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                    · linarith only [h105, h18, h2, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h105, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h108 | h108
      · linarith only [h0, h1, h108, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
        · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
          · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
            · linarith only [h108, h112, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h1, h112, hc23, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h111, hc35, hlam, hphi, ht23, u2ehi1]
        · linarith only [h0, h1, h110, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h117 | h117
    · rcases m.htr 0 2 3 (by decide) (by decide) with h118 | h118
      · rcases m.htr 0 3 4 (by decide) (by decide) with h119 | h119
        · rcases m.htr 0 3 5 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
            · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h117, h121, h125, h127, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases h3bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, h122, h123, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo1, u2ehi3]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, h126, h127, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1, u0elo1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            rcases p129_3 (m.d 0 3) (by simp) with h133 | h133
                            · rcases p129_3 (m.d 1 3) (by simp) with h134 | h134
                              · linarith only [h117, h134, hlam]
                              · linarith only [h123, h134, hlam]
                            · linarith only [h133, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            rcases p129_3 (m.d 0 3) (by simp) with h138 | h138
                            · rcases p129_3 (m.d 1 3) (by simp) with h139 | h139
                              · linarith only [h117, h139, hlam]
                              · linarith only [h124, h139, hlam]
                            · linarith only [h138, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h117, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, h126, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p129_1, u0elo1, u2ehi4]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1, u0elo1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, h127, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1, u0elo1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h118, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h121, hlam, p129_1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h118, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1, u0elo1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, h121, h127, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1, u0elo1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h119, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h123, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h125, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h127, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h120, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h124, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h126, hlam, p129_0]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [h0, h117, h120, hc34, hlam, hphi, ht0b, ht45, ht5b, p129_1, u0elo1]
                          · have p129_0 := h129c.1
                            have p129_1 := h129c.2.1
                            have p129_2 := h129c.2.2.1
                            have p129_3 := h129c.2.2.2
                            linarith only [hlam, p129_0]
                      · linarith only [h0, h117, h124, h126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h117, h119, h125, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h117, h120, h123, h124, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h117, h119, h121, h123, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h0, h122, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h117, h118, h119, h121, hlam, hphi, u0ehi8, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
            · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                  · linarith only [h117, h119, h120, h172, hlam, hphi, u0ehi8, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                      · linarith only [h119, h120, h175, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h0, h117, h169, h174, h177, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases h3bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h120, h170, h171, h177, hc45, hlam, hphi, ht23, ht34, p179_1, u2ehi3]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h120, h177, hc23, hc45, hlam, hphi, ht34, p179_1]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h120, h177, hc34, hc45, hlam, hphi, p179_1]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h120, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h117, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h0, h117, h119, h120, h177, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p179_1, u0ehi8, u2ehi2]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h0, h117, h119, h120, h177, hc12, hc34, hc45, hlam, hphi, ht01, p179_1, u0ehi8]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h172, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h118, hlam, p179_1]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h169, hlam, p179_1]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h118, h119, h120, h177, hc34, hc45, hlam, hphi, p179_1, u0ehi8, u0elo1]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h175, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h119, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h171, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h174, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h177, hlam, p179_0]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h119, h177, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p179_1, u0ehi8]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h170, h171, h177, hc45, hlam, hphi, ht23, ht34, p179_1, u2ehi3]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [h174, h177, hc45, hlam, hphi, ht23, ht34, p179_1, u2ehi3]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            rcases p179_3 (m.d 0 3) (by simp) with h203 | h203
                            · linarith only [h120, h203, hlam]
                            · linarith only [h119, h203, hlam]
                          · have p179_0 := h179c.1
                            have p179_1 := h179c.2.1
                            have p179_2 := h179c.2.2.1
                            have p179_3 := h179c.2.2.2
                            linarith only [hlam, p179_0]
                    · linarith only [h119, h120, h174, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4, u2ehi2]
                · linarith only [h119, h120, h171, hc13, hc35, hlam, hphi]
              · linarith only [h0, h170, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h117, h119, h169, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
          · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
            · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
              · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                · linarith only [h0, h117, h119, h214, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                    · linarith only [h0, h117, h119, h211, h212, h217, hc12, hlam, hphi, ht01, u0ehi9]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h219 | h219
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                        · rcases h3bigk with h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h212, h219, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1, u0elo2, u2ehi4]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h119, h219, hc34, hlam, hphi, ht23, p221_1, u2ehi4]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h119, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            rcases p221_3 (m.d 0 3) (by simp) with h226 | h226
                            · rcases p221_3 (m.d 1 3) (by simp) with h227 | h227
                              · linarith only [h117, h227, hlam]
                              · linarith only [h216, h227, hlam]
                            · linarith only [h226, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h117, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h0, h117, h219, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p221_1, u2ehi4]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h214, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h0, h117, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p221_1]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h118, hlam, p221_1]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h212, hlam, p221_1]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h217, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h118, h220, hc45, hlam, hphi, ht0b, ht5b, p221_1, u0elo1]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p221_1, u0ehi7]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h212, hc34, hlam, hphi, ht23, p221_1, u2ehi2]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p221_1, u2ehi2]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            rcases p221_3 (m.d 0 3) (by simp) with h245 | h245
                            · linarith only [h119, h245, hlam]
                            · linarith only [h211, h245, hlam]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h211, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h216, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h219, hlam, p221_0]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [h220, hlam, p221_1]
                          · have p221_0 := h221c.1
                            have p221_1 := h221c.2.1
                            have p221_2 := h221c.2.2.1
                            have p221_3 := h221c.2.2.2
                            linarith only [hlam, p221_0]
                        · linarith only [h0, h117, h119, h211, h212, h219, h220, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi9, u2ehi4]
                      · linarith only [h119, h211, h219, hc23, hc34, hlam, hphi]
                  · linarith only [h119, h211, h212, h216, hc34, hlam, hphi, ht23, u2ehi2]
              · linarith only [h0, h117, h212, h213, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h212, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
            · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
              · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                · linarith only [h117, h119, h260, hlam, hphi, u0ehi7, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h0, h117, h211, h262, hc12, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                    · linarith only [h119, h264, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h117, h211, h258, h266, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                        · rcases h3bigk with h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h258, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo2, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h211, h268, hc34, hlam, hphi, ht23, p269_1, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h119, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h211, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h117, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h0, h117, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p269_1, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h260, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h262, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h118, hlam, p269_1]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h258, hlam, p269_1]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h264, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h266, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p269_1, u0ehi7]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h258, hc34, hlam, hphi, ht23, p269_1, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p269_1, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h0, h117, h211, h258, hc12, hc34, hlam, hphi, ht01, ht23, p269_1, u0ehi7, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h0, h117, h258, hc12, hc35, hlam, hphi, ht01, ht23, p269_1, u0ehi7, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h258, hc35, hlam, hphi, ht23, p269_1, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hc35, hlam, hphi, ht23, p269_1, u2ehi2]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h268, hlam, p269_1]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                        · linarith only [h0, h117, h119, h258, h268, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u2ehi2]
              · linarith only [h0, h117, h258, h259, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h258, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · linarith only [h0, h117, h118, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h299 | h299
      · rcases m.htr 0 3 4 (by decide) (by decide) with h300 | h300
        · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
          · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
            · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
              · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
                · rcases m.htr 1 3 5 (by decide) (by decide) with h305 | h305
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h308 | h308
                        · linarith only [h299, h306, h308, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases h3bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h117, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h307, h308, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1, u0elo2]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 3) (by simp) with h314 | h314
                            · rcases p310_3 (m.d 1 3) (by simp) with h315 | h315
                              · rcases p310_3 (m.d 2 3) (by simp) with h316 | h316
                                · linarith only [h299, h316, hlam]
                                · linarith only [h306, h316, hlam]
                              · linarith only [h304, h315, hlam]
                            · linarith only [h314, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 3) (by simp) with h321 | h321
                            · rcases p310_3 (m.d 1 3) (by simp) with h322 | h322
                              · rcases p310_3 (m.d 2 3) (by simp) with h323 | h323
                                · linarith only [h299, h323, hlam]
                                · linarith only [h307, h323, hlam]
                              · linarith only [h305, h322, hlam]
                            · linarith only [h321, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h302, hc12, hlam, hphi, ht01, p310_1, u0ehi7]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 3) (by simp) with h330 | h330
                            · linarith only [h117, h330, hlam]
                            · linarith only [h299, h330, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 3) (by simp) with h333 | h333
                            · linarith only [h117, h333, hlam]
                            · linarith only [h300, h333, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            rcases p310_3 (m.d 0 3) (by simp) with h336 | h336
                            · linarith only [h117, h336, hlam]
                            · linarith only [h301, h336, hlam]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h299, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h302, hlam, p310_1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h299, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1, u0elo1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h299, h308, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1, u0elo1]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h300, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h304, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h306, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h308, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h301, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h305, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h307, hlam, p310_0]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [h301, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1, u0elo2]
                          · have p310_0 := h310c.1
                            have p310_1 := h310c.2.1
                            have p310_2 := h310c.2.2.1
                            have p310_3 := h310c.2.2.2
                            linarith only [hlam, p310_0]
                      · linarith only [h299, h301, h307, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                    · linarith only [h299, h300, h306, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h117, h299, h301, h305, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h117, h299, h300, h304, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h303, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h302, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
            · rcases m.htr 1 2 4 (by decide) (by decide) with h361 | h361
              · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                  · linarith only [h301, h360, h363, hc12, hlam, hphi, ht01, u0ehi7]
                  · linarith only [h117, h363, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h117, h300, h362, hlam, hphi, u0ehi5, u0elo2]
              · linarith only [h0, h361, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h299, h360, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
          · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
            · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
              · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                · linarith only [h300, h370, h372, hc12, hlam, hphi, ht01, u0ehi7]
                · linarith only [h117, h372, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
              · linarith only [h0, h371, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h299, h370, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h377 | h377
            · rcases m.htr 1 2 4 (by decide) (by decide) with h378 | h378
              · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                · linarith only [h117, h300, h377, h379, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h117, h379, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
              · linarith only [h0, h378, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h299, h377, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
        · rcases m.htr 0 3 5 (by decide) (by decide) with h385 | h385
          · rcases m.htr 1 2 3 (by decide) (by decide) with h386 | h386
            · linarith only [h299, h386, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h386, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
            · linarith only [h0, h299, h389, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h389, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h392 | h392
          · rcases m.htr 1 2 3 (by decide) (by decide) with h393 | h393
            · linarith only [h0, h299, h393, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h393, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
            · linarith only [h0, h299, h396, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h396, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
