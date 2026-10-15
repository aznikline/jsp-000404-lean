import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
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
                                  · linarith only [h0, h10, h17, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h0, h10, h14, h16, h17, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                                  · linarith only [h0, h10, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h0, h10, h14, h21, h22, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h10, h13, h21, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h0, h13, h14, h26, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                                  · linarith only [h10, h14, h29, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                                    · linarith only [h11, h26, h31, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                                      · linarith only [h0, h10, h11, h14, h26, h28, h33, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h0bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h14, h33, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, h14, h33, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, h14, h33, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
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
                                          linarith only [h10, h14, h33, h7, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, h10, h14, h33, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, h10, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h1, hlam, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h4, hlam, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, h14, h33, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h0, h10, h14, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h2, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h5, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h7, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h10, h14, h8, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p35_1, u2ehi2]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h3, hlam, p35_0]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h6, hlam, p35_1]
                                        · have p35_0 := h35c.1
                                          have p35_1 := h35c.2.1
                                          have p35_2 := h35c.2.2.1
                                          have p35_3 := h35c.2.2.2
                                          linarith only [h8, hlam, p35_0]
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
                                · linarith only [h13, h14, h28, h8, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                            · linarith only [h0, h13, h4, h62, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                                · linarith only [h0, h13, h4, h64, h65, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                                  · linarith only [h10, h62, h67, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                                    · linarith only [h0, h11, h69, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h64, h69, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                                · linarith only [h10, h13, h72, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                                  · linarith only [h10, h62, h74, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                                    · linarith only [h10, h13, h64, h76, hc24, hlam, hphi, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                                      · linarith only [h10, h13, h64, h78, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h10, h13, h7, h78, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h83 | h83
                      · linarith only [h10, h83, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h0, h10, h4, h85, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                                      · linarith only [h0, h10, h4, h87, h93, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · rcases h0bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h4, h85, h90, h92, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h2, h7, h89, h93, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p95_1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h2, h89, h93, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p95_1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h6, h85, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h0, hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h4, h85, h90, h92, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h0, h5, h85, h92, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h0, h6, h85, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h1, hlam, p95_1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h4, hlam, p95_1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h5, h85, h92, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h0, h4, h6, h85, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h2, hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h5, hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h7, hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h6, h85, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p95_1, u2ehi1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h3, hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h6, hlam, p95_1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h8, hlam, p95_0]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [h9, hlam, p95_1]
                                        · have p95_0 := h95c.1
                                          have p95_1 := h95c.2.1
                                          have p95_2 := h95c.2.2.1
                                          have p95_3 := h95c.2.2.2
                                          linarith only [hlam, p95_0]
                                    · linarith only [h2, h89, h92, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h83, h90, h91, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h10, h4, h7, h87, h89, h90, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                                    · linarith only [h124, h126, h83, h89, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h126, h83, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h10, h125, h88, hlam]
                                · linarith only [h0, h10, h124, h4, h7, h87, h88, h89, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h0, h131, h4, h8, h87, h88, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h133 | h133
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h134 | h134
                                  · linarith only [h0, h134, h4, h87, h88, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h10, h134, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h10, h133, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h0, h138, h4, h7, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                                · linarith only [h0, h140, h141, h4, h87, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h0, h10, h141, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                                · linarith only [h10, h144, h87, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h10, h144, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                              · linarith only [h152, h2, h9, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                                  · linarith only [h0, h147, h155, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h1, h151, h154, h155, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h154, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                              · linarith only [h159, h2, h9, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                                  · linarith only [h0, h147, h151, h162, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                                    · linarith only [h148, h150, h151, h164, h8, h9, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h166 | h166
                                      · linarith only [h148, h150, h151, h166, h8, h9, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h0bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h161, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h148, h150, h151, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          rcases p168_3 (m.d 0 1) (by simp) with h172 | h172
                                          · rcases p168_3 (m.d 0 2) (by simp) with h173 | h173
                                            · linarith only [h0, h173, hlam]
                                            · linarith only [h173, h5, hlam]
                                          · linarith only [h172, h2, hlam]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h148, h150, h151, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h0, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h148, h150, h151, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          rcases p168_3 (m.d 0 1) (by simp) with h181 | h181
                                          · rcases p168_3 (m.d 0 2) (by simp) with h182 | h182
                                            · rcases p168_3 (m.d 0 3) (by simp) with h183 | h183
                                              · linarith only [h183, h4, hlam]
                                              · linarith only [h183, h7, hlam]
                                            · linarith only [h182, h5, hlam]
                                          · linarith only [h181, h2, hlam]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h0, h148, h150, h151, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h1, hlam, p168_1]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h4, hlam, p168_1]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          rcases p168_3 (m.d 0 1) (by simp) with h192 | h192
                                          · rcases p168_3 (m.d 0 2) (by simp) with h193 | h193
                                            · rcases p168_3 (m.d 0 3) (by simp) with h194 | h194
                                              · rcases p168_3 (m.d 0 4) (by simp) with h195 | h195
                                                · linarith only [h195, h7, hlam]
                                                · rcases p168_3 (m.d 0 5) (by simp) with h197 | h197
                                                  · linarith only [h197, h8, hlam]
                                                  · linarith only [h197, h9, hlam]
                                              · linarith only [h194, h7, hlam]
                                            · linarith only [h193, h5, hlam]
                                          · linarith only [h192, h2, hlam]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h148, h150, h151, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h2, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h5, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h7, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h9, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h3, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h6, hlam, p168_1]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h8, hlam, p168_0]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [h148, h2, h9, hc45, hlam, hphi, ht23, ht34, p168_1, u2ehi3]
                                        · have p168_0 := h168c.1
                                          have p168_1 := h168c.2.1
                                          have p168_2 := h168c.2.2.1
                                          have p168_3 := h168c.2.2.2
                                          linarith only [hlam, p168_0]
                                · linarith only [h161, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h147, h150, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h147, h149, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h147, h148, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
                      · linarith only [h147, h218, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h218, h5, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h221, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                            · linarith only [h1, h227, h8, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h229 | h229
                              · linarith only [h2, h221, h229, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h232 | h232
                                  · linarith only [h0, h2, h223, h224, h232, h7, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                                    · linarith only [h2, h221, h224, h234, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                                      · linarith only [h2, h221, h224, h236, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h0bigk with h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h231, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          rcases p238_3 (m.d 0 1) (by simp) with h241 | h241
                                          · rcases p238_3 (m.d 0 2) (by simp) with h242 | h242
                                            · linarith only [h0, h242, hlam]
                                            · linarith only [h242, h4, hlam]
                                          · linarith only [h1, h241, hlam]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          rcases p238_3 (m.d 0 1) (by simp) with h246 | h246
                                          · rcases p238_3 (m.d 0 2) (by simp) with h247 | h247
                                            · linarith only [h0, h247, hlam]
                                            · linarith only [h247, h5, hlam]
                                          · linarith only [h2, h246, hlam]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          rcases p238_3 (m.d 0 1) (by simp) with h251 | h251
                                          · rcases p238_3 (m.d 0 2) (by simp) with h252 | h252
                                            · linarith only [h0, h252, hlam]
                                            · linarith only [h252, h6, hlam]
                                          · linarith only [h251, h3, hlam]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h0, hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          rcases p238_3 (m.d 0 1) (by simp) with h258 | h258
                                          · rcases p238_3 (m.d 0 2) (by simp) with h259 | h259
                                            · rcases p238_3 (m.d 0 3) (by simp) with h260 | h260
                                              · linarith only [h260, h4, hlam]
                                              · rcases p238_3 (m.d 0 4) (by simp) with h262 | h262
                                                · linarith only [h262, h5, hlam]
                                                · rcases p238_3 (m.d 0 5) (by simp) with h264 | h264
                                                  · linarith only [h264, h6, hlam]
                                                  · linarith only [h264, h8, hlam]
                                            · linarith only [h259, h4, hlam]
                                          · linarith only [h1, h258, hlam]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          rcases p238_3 (m.d 0 1) (by simp) with h269 | h269
                                          · rcases p238_3 (m.d 0 2) (by simp) with h270 | h270
                                            · rcases p238_3 (m.d 0 3) (by simp) with h271 | h271
                                              · linarith only [h271, h4, hlam]
                                              · linarith only [h271, h7, hlam]
                                            · linarith only [h270, h5, hlam]
                                          · linarith only [h2, h269, hlam]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          rcases p238_3 (m.d 0 1) (by simp) with h276 | h276
                                          · rcases p238_3 (m.d 0 2) (by simp) with h277 | h277
                                            · rcases p238_3 (m.d 0 3) (by simp) with h278 | h278
                                              · linarith only [h278, h4, hlam]
                                              · rcases p238_3 (m.d 0 4) (by simp) with h280 | h280
                                                · linarith only [h280, h5, hlam]
                                                · rcases p238_3 (m.d 0 5) (by simp) with h282 | h282
                                                  · linarith only [h282, h6, hlam]
                                                  · rcases h3bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h224, h226, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p238_1, p284_1, u2ehi3]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h0, h231, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p238_1, p284_1, u2ehi3]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, p284_1]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h8, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h1, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h1, h231, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p284_1, u2ehi3]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h0, h1, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p238_1, p284_1]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h227, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h4, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h223, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h0, h225, h232, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p284_1]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h232, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h7, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h226, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h231, hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [hlam, p284_0]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h236, hlam, p284_1]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h236, h4, hc45, hlam, hphi, ht23, ht34, p284_1, u2ehi2]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h223, h236, hc45, hlam, hphi, ht23, ht34, p284_1, u2ehi2]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [h231, h236, hc45, hlam, hphi, ht23, ht34, p284_1, u2ehi3]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      rcases p284_3 (m.d 0 3) (by simp) with h308 | h308
                                                      · linarith only [h308, h8, hlam]
                                                      · linarith only [h308, h7, hlam]
                                                    · have p284_0 := h284c.1
                                                      have p284_1 := h284c.2.1
                                                      have p284_2 := h284c.2.2.1
                                                      have p284_3 := h284c.2.2.2
                                                      linarith only [hlam, p284_0]
                                            · linarith only [h277, h6, hlam]
                                          · linarith only [h276, h3, hlam]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h1, hlam, p238_1]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h4, hlam, p238_1]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h2, h224, h236, h8, hc45, hlam, hphi, ht23, ht34, p238_1, u2ehi3]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h8, hlam, p238_1]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h2, hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h5, hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h7, hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h221, hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h3, hlam, p238_0]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h6, hlam, p238_1]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h1, h224, h226, h236, h8, hc45, hlam, hphi, ht23, ht34, p238_1, u2ehi3]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [h2, h224, h236, h8, hc45, hlam, hphi, ht23, ht34, p238_1, u2ehi3]
                                        · have p238_0 := h238c.1
                                          have p238_1 := h238c.2.1
                                          have p238_2 := h238c.2.2.1
                                          have p238_3 := h238c.2.2.2
                                          linarith only [hlam, p238_0]
                                · linarith only [h231, h7, h8, hc23, hc35, hlam, hphi]
                          · linarith only [h226, h7, h8, hc13, hc35, hlam, hphi]
                        · linarith only [h223, h225, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h223, h224, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h223, h4, h8, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h334 | h334
                · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h339 | h339
                          · linarith only [h334, h339, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h341 | h341
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h342 | h342
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                                · linarith only [h1, h341, h343, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h345 | h345
                                  · linarith only [h0, h337, h343, h345, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                                  · linarith only [h1, h341, h345, h7, hc23, hc34, hlam, hphi]
                              · linarith only [h335, h339, h341, h342, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h334, h341, h7, hc13, hc34, hlam, hphi]
                        · linarith only [h337, h338, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h336, h337, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h336, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h334, h335, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h357 | h357
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                          · linarith only [h1, h358, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                            · linarith only [h1, h334, h360, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                                · linarith only [h1, h355, h363, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                                  · linarith only [h1, h334, h355, h365, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h367 | h367
                                    · linarith only [h0, h356, h367, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · linarith only [h2, h362, h367, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h354, h356, h362, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h355, h357, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h355, h356, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h355, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h376 | h376
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                          · linarith only [h1, h377, h7, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
                            · linarith only [h1, h334, h379, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h1, h2, h354, h374, h381, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h383 | h383
                                · linarith only [h1, h374, h383, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
                                  · linarith only [h1, h334, h374, h385, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
                                    · linarith only [h1, h354, h374, h375, h387, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h389 | h389
                                      · linarith only [h1, h354, h374, h389, h7, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h1, h374, h389, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h374, h376, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h374, h375, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h374, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h397 | h397
          · linarith only [h397, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h399 | h399
            · linarith only [h399, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h401 | h401
              · rcases m.htr 0 3 5 (by decide) (by decide) with h402 | h402
                · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                    · linarith only [h0, h4, h404, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
                      · linarith only [h0, h397, h406, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h408 | h408
                        · linarith only [h0, h399, h408, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                                      · linarith only [h1, h410, h416, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                      · rcases h0bigk with h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          rcases p418_3 (m.d 0 1) (by simp) with h420 | h420
                                          · rcases p418_3 (m.d 0 2) (by simp) with h421 | h421
                                            · linarith only [h0, h421, hlam]
                                            · rcases p418_3 (m.d 0 3) (by simp) with h423 | h423
                                              · linarith only [h1, h423, hlam]
                                              · linarith only [h4, h423, hlam]
                                          · linarith only [h0, h420, hlam]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h2, h401, h412, h416, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h2, h412, h416, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          rcases p418_3 (m.d 0 1) (by simp) with h429 | h429
                                          · rcases p418_3 (m.d 0 2) (by simp) with h430 | h430
                                            · linarith only [h0, h430, hlam]
                                            · rcases p418_3 (m.d 0 3) (by simp) with h432 | h432
                                              · linarith only [h1, h432, hlam]
                                              · linarith only [h402, h432, hlam]
                                          · linarith only [h3, h429, hlam]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h0, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h4, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h397, hlam, p418_1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h399, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h1, hlam, p418_1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h0, h4, hc23, hlam, hphi, p418_1, u2ehi1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h2, h4, h412, h416, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p418_1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h0, h399, h4, hc23, hlam, hphi, p418_1, u2ehi1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h2, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h0, h397, hc24, hlam, hphi, p418_1, u2ehi1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h401, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h0, h399, h4, h401, hc23, hlam, hphi, p418_1, u2ehi1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h3, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h0, h399, hc25, hlam, hphi, p418_1, u2ehi1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h402, hlam, p418_0]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [h403, hlam, p418_1]
                                        · have p418_0 := h418c.1
                                          have p418_1 := h418c.2.1
                                          have p418_2 := h418c.2.2.1
                                          have p418_3 := h418c.2.2.2
                                          linarith only [hlam, p418_0]
                                    · linarith only [h2, h412, h415, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h0, h4, h414, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h4, h413, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h4, h401, h403, h406, h412, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h4, h402, h404, h411, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h4, h401, h404, h410, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                    · linarith only [h0, h397, h4, h402, h462, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h464 | h464
                      · linarith only [h0, h397, h403, h464, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                        · linarith only [h0, h397, h403, h466, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h470 | h470
                              · linarith only [h1, h397, h403, h468, h470, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h472 | h472
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                                    · linarith only [h0, h397, h403, h474, hc24, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h397, h474, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h0, h4, h473, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h1, h4, h468, h472, hlam]
                            · linarith only [h4, h402, h462, h469, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h4, h401, h462, h468, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                  · linarith only [h401, h402, h481, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
                    · linarith only [h0, h397, h483, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
                      · linarith only [h0, h4, h485, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
                        · linarith only [h0, h399, h487, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h489 | h489
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h490 | h490
                            · linarith only [h1, h397, h401, h402, h490, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
                              · linarith only [h0, h2, h397, h481, h492, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h495 | h495
                                  · linarith only [h0, h397, h401, h402, h495, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h4, h495, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h1, h4, h489, h494, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h401, h402, h489, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h500 | h500
                · rcases m.htr 0 4 5 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                    · linarith only [h0, h397, h502, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                      · linarith only [h0, h4, h504, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                        · linarith only [h0, h399, h401, h500, h506, hc34, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                          · linarith only [h1, h399, h401, h500, h508, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                                · linarith only [h1, h401, h510, h512, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                · linarith only [h4, h512, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h397, h501, h504, h511, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h401, h500, h510, hc13, hc34, hlam, hphi]
                  · linarith only [h401, h500, h501, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h518 | h518
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
                    · linarith only [h0, h4, h519, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h521 | h521
                      · linarith only [h0, h4, h521, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h523 | h523
                        · linarith only [h0, h399, h523, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
                          · linarith only [h1, h4, h401, h525, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                            · linarith only [h0, h1, h4, h500, h527, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                                · linarith only [h0, h4, h401, h530, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h530, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h401, h518, h521, h529, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
                    · linarith only [h0, h4, h534, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                      · linarith only [h0, h4, h536, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
                        · linarith only [h0, h399, h538, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                          · linarith only [h1, h401, h540, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                            · linarith only [h1, h500, h542, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
                              · linarith only [h2, h4, h401, h518, h544, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h546 | h546
                                · linarith only [h0, h4, h401, h546, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h546, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h549 | h549
        · rcases m.htr 0 2 4 (by decide) (by decide) with h550 | h550
          · rcases m.htr 0 2 5 (by decide) (by decide) with h551 | h551
            · linarith only [h0, h3, h551, hlam]
            · linarith only [h549, h551, hc25, hlam, hphi, u2ehi2]
          · linarith only [h549, h550, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h555 | h555
          · linarith only [h549, h555, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h557 | h557
            · linarith only [h549, h557, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
              · rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
                · linarith only [h1, h3, h560, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h562 | h562
                  · linarith only [h0, h3, h559, h560, h562, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                    · linarith only [h0, h3, h564, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
                      · linarith only [h1, h3, h555, h564, h566, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h568 | h568
                        · linarith only [h0, h549, h568, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h564, h568, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h571 | h571
                · linarith only [h0, h3, h559, h571, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                  · linarith only [h2, h3, h573, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
                    · linarith only [h0, h3, h575, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h577 | h577
                      · linarith only [h1, h3, h555, h575, h577, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
                        · linarith only [h0, h549, h579, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h575, h579, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h582 | h582
      · rcases m.htr 0 2 3 (by decide) (by decide) with h583 | h583
        · rcases m.htr 0 2 4 (by decide) (by decide) with h584 | h584
          · linarith only [h0, h2, h584, hlam]
          · linarith only [h583, h584, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h587 | h587
          · linarith only [h583, h587, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h589 | h589
            · linarith only [h583, h589, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h591 | h591
              · linarith only [h1, h2, h591, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
                · rcases m.htr 0 4 5 (by decide) (by decide) with h594 | h594
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                    · linarith only [h0, h2, h583, h595, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
                      · linarith only [h0, h2, h582, h583, h587, h597, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h1, h2, h595, h597, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h594, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h602 | h602
                    · linarith only [h0, h2, h602, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h604 | h604
                      · linarith only [h1, h2, h602, h604, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h602, h604, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h601, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h608 | h608
        · rcases m.htr 0 2 4 (by decide) (by decide) with h609 | h609
          · linarith only [h0, h2, h609, hlam]
          · linarith only [h608, h609, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h612 | h612
          · linarith only [h608, h612, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h614 | h614
            · linarith only [h608, h614, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h616 | h616
              · linarith only [h1, h2, h616, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h618 | h618
                · linarith only [h0, h582, h616, h618, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                    · linarith only [h0, h2, h621, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                      · linarith only [h1, h2, h612, h621, h623, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h2, h623, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h620, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h627 | h627
    · rcases m.htr 0 1 5 (by decide) (by decide) with h628 | h628
      · rcases m.htr 0 2 3 (by decide) (by decide) with h629 | h629
        · linarith only [h0, h1, h629, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h631 | h631
          · linarith only [h629, h631, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h633 | h633
            · linarith only [h629, h633, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h635 | h635
              · rcases m.htr 0 3 5 (by decide) (by decide) with h636 | h636
                · rcases m.htr 0 4 5 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h638 | h638
                    · linarith only [h0, h1, h638, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h638, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h641 | h641
                    · linarith only [h0, h1, h641, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h641, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h636, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h635, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h646 | h646
        · linarith only [h0, h1, h646, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h648 | h648
          · linarith only [h646, h648, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h650 | h650
            · linarith only [h646, h650, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h652 | h652
              · rcases m.htr 0 3 5 (by decide) (by decide) with h653 | h653
                · rcases m.htr 0 4 5 (by decide) (by decide) with h654 | h654
                  · linarith only [h627, h628, h654, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h656 | h656
                    · linarith only [h0, h1, h656, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h656, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h653, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h652, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h661 | h661
      · rcases m.htr 0 2 3 (by decide) (by decide) with h662 | h662
        · linarith only [h0, h1, h662, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h664 | h664
          · linarith only [h662, h664, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h666 | h666
            · linarith only [h662, h666, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h668 | h668
              · rcases m.htr 0 3 5 (by decide) (by decide) with h669 | h669
                · rcases m.htr 0 4 5 (by decide) (by decide) with h670 | h670
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h671 | h671
                    · linarith only [h0, h1, h671, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h671, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h627, h670, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h627, h668, h669, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h668, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h677 | h677
        · linarith only [h0, h1, h677, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h679 | h679
          · linarith only [h677, h679, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h681 | h681
            · linarith only [h677, h681, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h683 | h683
              · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
                · rcases m.htr 0 4 5 (by decide) (by decide) with h685 | h685
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h686 | h686
                    · linarith only [h0, h677, h686, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h686, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h627, h685, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h684, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h683, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h693 | h693
  · rcases m.htr 0 1 5 (by decide) (by decide) with h694 | h694
    · rcases m.htr 0 2 3 (by decide) (by decide) with h695 | h695
      · rcases m.htr 0 2 4 (by decide) (by decide) with h696 | h696
        · rcases m.htr 0 2 5 (by decide) (by decide) with h697 | h697
          · rcases m.htr 0 3 4 (by decide) (by decide) with h698 | h698
            · rcases m.htr 0 3 5 (by decide) (by decide) with h699 | h699
              · rcases m.htr 0 4 5 (by decide) (by decide) with h700 | h700
                · rcases m.htr 1 2 3 (by decide) (by decide) with h701 | h701
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h702 | h702
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h703 | h703
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h704 | h704
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h705 | h705
                          · linarith only [h0, h692, h705, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h692, h699, h704, h705, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h692, h698, h701, h704, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h694, h697, h703, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h692, h701, h702, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h692, h698, h700, h701, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h713 | h713
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h714 | h714
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h715 | h715
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                          · linarith only [h0, h692, h716, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h692, h699, h715, h716, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h692, h698, h712, h715, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h694, h714, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h694, h713, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h692, h699, h712, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h723 | h723
                · linarith only [h698, h699, h723, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h725 | h725
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h726 | h726
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h727 | h727
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
                          · linarith only [h0, h692, h699, h729, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                            · linarith only [h0, h694, h723, h728, h729, h731, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h733 | h733
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
                                · linarith only [h692, h699, h725, h734, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                                  · linarith only [h693, h723, h726, h736, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                                    · linarith only [h0, h693, h694, h723, h725, h726, h729, h733, h738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h0, hlam, p740_1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h0, h692, h725, h733, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p740_1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h0, h693, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p740_1, u2ehi3]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p740_1, u5ehi0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h0, h694, hc12, hlam, hphi, ht01, ht0b, ht5b, p740_1, u5ehi1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        rcases p740_3 (m.d 0 1) (by simp) with h748 | h748
                                        · linarith only [h0, h748, hlam]
                                        · linarith only [h692, h748, hlam]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        rcases p740_3 (m.d 0 1) (by simp) with h751 | h751
                                        · linarith only [h0, h751, hlam]
                                        · linarith only [h693, h751, hlam]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        rcases p740_3 (m.d 0 1) (by simp) with h754 | h754
                                        · linarith only [h0, h754, hlam]
                                        · linarith only [h694, h754, hlam]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h692, hlam, p740_1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h695, hlam, p740_1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h693, h699, h726, hc35, hlam, hphi, ht23, p740_1, u2ehi3]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h699, hlam, p740_1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h693, hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h696, hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h698, hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h723, hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h694, hlam, p740_0]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h697, hlam, p740_1]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h0, h692, h694, h726, h728, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p740_1, u2ehi3]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [h693, h699, h726, hc35, hlam, hphi, ht23, p740_1, u2ehi3]
                                      · have p740_0 := h740c.1
                                        have p740_1 := h740c.2.1
                                        have p740_2 := h740c.2.2.1
                                        have p740_3 := h740c.2.2.2
                                        linarith only [hlam, p740_0]
                              · linarith only [h0, h692, h698, h733, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h698, h699, h728, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h692, h725, h727, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h692, h725, h726, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h696, h725, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h777 | h777
              · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
                · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h780 | h780
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h781 | h781
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h782 | h782
                        · linarith only [h692, h698, h777, h782, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h784 | h784
                          · linarith only [h0, h693, h782, h784, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h698, h777, h779, h784, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h693, h778, h781, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h692, h779, h780, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h692, h777, h779, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h698, h777, h778, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h791 | h791
                · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h793 | h793
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h794 | h794
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h795 | h795
                        · linarith only [h692, h698, h795, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h797 | h797
                          · linarith only [h692, h777, h797, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                            · linarith only [h0, h693, h799, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h693, h791, h792, h795, h799, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h692, h792, h794, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h692, h792, h793, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h693, h791, h792, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h806 | h806
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                        · linarith only [h692, h698, h808, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                          · linarith only [h692, h777, h810, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h812 | h812
                            · linarith only [h0, h693, h791, h812, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h814 | h814
                              · linarith only [h692, h698, h805, h814, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h816 | h816
                                · linarith only [h0, h694, h777, h805, h808, h812, h816, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h818 | h818
                                  · linarith only [h693, h791, h806, h818, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h820 | h820
                                    · linarith only [h693, h791, h805, h808, h820, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h692, h698, h805, h820, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h694, h807, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h692, h805, h806, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h693, h696, h805, hc23, hlam, hphi, u2ehi3]
          · linarith only [h695, h697, hc25, hlam, hphi, u2ehi2]
        · linarith only [h695, h696, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h692, h695, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h829 | h829
      · rcases m.htr 0 2 4 (by decide) (by decide) with h830 | h830
        · rcases m.htr 0 2 5 (by decide) (by decide) with h831 | h831
          · rcases m.htr 0 3 4 (by decide) (by decide) with h832 | h832
            · rcases m.htr 0 3 5 (by decide) (by decide) with h833 | h833
              · linarith only [h692, h694, h833, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
                · linarith only [h692, h694, h832, h835, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                          · linarith only [h692, h694, h833, h839, h841, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h692, h694, h838, h840, h841, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h832, h833, h840, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h831, h839, hlam]
                    · linarith only [h0, h692, h837, h838, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h831, h837, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h848 | h848
              · linarith only [h693, h694, h832, h848, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h850 | h850
                · linarith only [h693, h694, h850, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h852 | h852
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h854 | h854
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
                        · linarith only [h692, h694, h832, h854, h855, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h857 | h857
                          · linarith only [h693, h694, h848, h855, h857, hlam]
                          · linarith only [h693, h694, h852, h855, h857, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h693, h831, h853, h854, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h692, h852, h853, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h831, h852, hc23, hlam, hphi, u2ehi4]
          · linarith only [h829, h831, hc25, hlam, hphi, u2ehi2]
        · linarith only [h829, h830, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h692, h829, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h866 | h866
    · rcases m.htr 0 2 3 (by decide) (by decide) with h867 | h867
      · rcases m.htr 0 2 4 (by decide) (by decide) with h868 | h868
        · rcases m.htr 0 2 5 (by decide) (by decide) with h869 | h869
          · rcases m.htr 0 3 4 (by decide) (by decide) with h870 | h870
            · linarith only [h692, h693, h870, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h872 | h872
              · rcases m.htr 0 4 5 (by decide) (by decide) with h873 | h873
                · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h876 | h876
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                        · linarith only [h692, h870, h872, h877, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h692, h693, h874, h877, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h692, h693, h874, h875, h876, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h868, h875, hlam]
                  · linarith only [h0, h868, h874, hc23, hlam, hphi, u2ehi3]
                · linarith only [h692, h693, h872, h873, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
                · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h888 | h888
                        · linarith only [h692, h693, h870, h886, h888, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h692, h693, h885, h888, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h692, h693, h885, h886, h887, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h692, h885, h886, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h866, h885, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h693, h866, h884, hlam]
          · linarith only [h867, h869, hc25, hlam, hphi, u2ehi2]
        · linarith only [h867, h868, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h692, h867, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h898 | h898
      · rcases m.htr 0 2 4 (by decide) (by decide) with h899 | h899
        · rcases m.htr 0 2 5 (by decide) (by decide) with h900 | h900
          · rcases m.htr 0 3 4 (by decide) (by decide) with h901 | h901
            · linarith only [h692, h693, h901, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h903 | h903
              · linarith only [h692, h866, h903, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h905 | h905
                · rcases m.htr 1 2 3 (by decide) (by decide) with h906 | h906
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h907 | h907
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h908 | h908
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
                        · linarith only [h692, h866, h901, h909, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h692, h693, h906, h909, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h692, h693, h900, h906, h907, h908, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h692, h899, h906, h907, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h899, h906, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h915 | h915
                  · linarith only [h692, h693, h905, h915, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h692, h898, h915, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h898, h900, hc25, hlam, hphi, u2ehi2]
        · linarith only [h898, h899, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h692, h898, hlam]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h922 | h922
  · rcases m.htr 0 2 3 (by decide) (by decide) with h923 | h923
    · rcases m.htr 0 2 4 (by decide) (by decide) with h924 | h924
      · rcases m.htr 0 2 5 (by decide) (by decide) with h925 | h925
        · rcases m.htr 0 3 4 (by decide) (by decide) with h926 | h926
          · rcases m.htr 0 3 5 (by decide) (by decide) with h927 | h927
            · rcases m.htr 0 4 5 (by decide) (by decide) with h928 | h928
              · rcases m.htr 1 2 3 (by decide) (by decide) with h929 | h929
                · rcases m.htr 1 2 4 (by decide) (by decide) with h930 | h930
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h933 | h933
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
                          · linarith only [h692, h921, h934, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h692, h921, h928, h929, h930, h934, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h692, h922, h933, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h692, h921, h926, h932, hlam]
                    · linarith only [h692, h922, h929, h931, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h692, h922, h929, h930, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h921, h923, h928, h929, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h942 | h942
                · rcases m.htr 1 2 4 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h944 | h944
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h945 | h945
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h946 | h946
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h947 | h947
                          · linarith only [h692, h921, h928, h947, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h949 | h949
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h950 | h950
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h951 | h951
                                · linarith only [h921, h928, h943, h951, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h953 | h953
                                  · linarith only [h921, h928, h943, h949, h953, hlam]
                                  · rcases h0bigk with h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, hlam, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h692, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h692, h921, h942, h943, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p955_1, u2ehi3]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h692, h942, hc12, hlam, hphi, ht01, ht0b, ht5b, p955_1, u5ehi0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, h922, hc12, hlam, hphi, ht01, ht0b, ht5b, p955_1, u5ehi1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, h692, h922, h944, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p955_1, u2ehi4]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      rcases p955_3 (m.d 0 1) (by simp) with h964 | h964
                                      · linarith only [h0, h964, hlam]
                                      · linarith only [h921, h964, hlam]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      rcases p955_3 (m.d 0 1) (by simp) with h967 | h967
                                      · linarith only [h0, h967, hlam]
                                      · linarith only [h922, h967, hlam]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h922, h943, h947, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p955_1, u2ehi3]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h923, hlam, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      rcases p955_3 (m.d 0 1) (by simp) with h973 | h973
                                      · linarith only [h692, h973, hlam]
                                      · linarith only [h921, h973, hlam]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      rcases p955_3 (m.d 0 1) (by simp) with h976 | h976
                                      · linarith only [h692, h976, hlam]
                                      · linarith only [h922, h976, hlam]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h921, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h924, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h926, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h928, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h922, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h925, hlam, p955_1]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h927, hlam, p955_0]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [h0, h921, h922, h943, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p955_1, u2ehi3]
                                    · have p955_0 := h955c.1
                                      have p955_1 := h955c.2.1
                                      have p955_2 := h955c.2.2.1
                                      have p955_3 := h955c.2.2.2
                                      linarith only [hlam, p955_0]
                              · linarith only [h692, h922, h942, h946, h950, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h926, h928, h949, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h692, h922, h946, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h692, h921, h926, h943, h945, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h692, h921, h942, h943, h944, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h692, h922, h925, h942, h943, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h922, h942, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h692, h922, h927, hlam]
          · linarith only [h692, h921, h926, hlam]
        · linarith only [h923, h925, hc25, hlam, hphi, u2ehi2]
      · linarith only [h923, h924, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1000 | h1000
      · linarith only [h1000, h923, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h1000, h921, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1003 | h1003
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1004 | h1004
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1005 | h1005
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1006 | h1006
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1007 | h1007
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1008 | h1008
              · linarith only [h1008, h921, h922, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1011 | h1011
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1014 | h1014
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                          · linarith only [h1008, h1010, h1014, h1015, h921, h922, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1011, h1015, h921, h922, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · linarith only [h1003, h1007, h1011, h1014, h692, h921, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1011, h1013, h692, h921, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h1003, h1012, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1005, h1011, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1005, h1010, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1023 | h1023
              · linarith only [h1023, h921, h922, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1025 | h1025
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1026 | h1026
                  · linarith only [h1007, h1026, h692, h921, hc35, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h1005, h1026, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1003, h1025, h921, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1006, h692, h921, hlam]
        · linarith only [h1003, h1005, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1003, h1004, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1033 | h1033
      · linarith only [h1003, h1033, hc23, hlam, hphi, u2ehi3]
      · linarith only [h0, h1033, h921, hlam]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1037 | h1037
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1038 | h1038
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1039 | h1039
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1040 | h1040
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1041 | h1041
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1042 | h1042
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1043 | h1043
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1044 | h1044
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1045 | h1045
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1046 | h1046
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1047 | h1047
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1048 | h1048
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1049 | h1049
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1050 | h1050
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1051 | h1051
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1052 | h1052
                                · linarith only [h1037, h1049, h1052, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h0bigk with h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h0, hlam, p1054_1]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h692, hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h921, hlam, p1054_1]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1046, h921, hc13, hlam, hphi, ht01, ht0b, ht5b, p1054_1, u5ehi0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h0, h1036, h1045, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u2ehi4]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h0, h1036, h1045, h692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u2ehi4]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h0, h1036, h1045, h921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u2ehi4]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    rcases p1054_3 (m.d 0 1) (by simp) with h1064 | h1064
                                    · linarith only [h0, h1064, hlam]
                                    · linarith only [h1036, h1064, hlam]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1036, h1045, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u2ehi4]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1037, hlam, p1054_1]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1036, h1043, h1045, h692, h921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u2ehi4]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    rcases p1054_3 (m.d 0 1) (by simp) with h1071 | h1071
                                    · linarith only [h1071, h692, hlam]
                                    · linarith only [h1036, h1071, hlam]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1036, h1045, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1, u2ehi4]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1038, hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1040, hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    rcases p1054_3 (m.d 0 1) (by simp) with h1078 | h1078
                                    · linarith only [h1078, h921, hlam]
                                    · linarith only [h1036, h1078, hlam]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1036, hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1039, hlam, p1054_1]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1041, hlam, p1054_0]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [h1042, hlam, p1054_1]
                                  · have p1054_0 := h1054c.1
                                    have p1054_1 := h1054c.2.1
                                    have p1054_2 := h1054c.2.2.1
                                    have p1054_3 := h1054c.2.2.2
                                    linarith only [hlam, p1054_0]
                              · linarith only [h1036, h1043, h1046, h1048, h1051, h921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1036, h1043, h1046, h1047, h1050, h921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1088 | h1088
                            · linarith only [h1040, h1043, h1049, h1088, h692, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h1036, h1043, h1046, h1047, h1088, h921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1036, h1048, h921, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h1036, h1045, h1046, h1047, h921, hc35, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h1040, h1046, h692, hlam]
                  · linarith only [h0, h1038, h1045, hc25, hlam, hphi, u2ehi3]
                · linarith only [h1036, h1043, h1044, h692, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1038, h1043, hc23, hlam, hphi, u2ehi3]
            · linarith only [h1036, h1042, h921, hlam]
          · linarith only [h1036, h1041, h692, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1099 | h1099
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1102 | h1102
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1103 | h1103
                  · linarith only [h1036, h1040, h1103, h692, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h1036, h1101, h1103, h692, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h1036, h1038, h1101, h1102, h692, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h1038, h1101, hc23, hlam, hphi, u2ehi3]
            · linarith only [h1036, h1040, h1100, h692, hlam]
          · linarith only [h1036, h1099, h692, hlam]
      · linarith only [h1038, h1039, hc25, hlam, hphi, u2ehi3]
    · linarith only [h1037, h1038, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1112 | h1112
    · linarith only [h1037, h1112, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1114 | h1114
      · linarith only [h1037, h1114, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h1036, h1114, hlam]

end R2N4
