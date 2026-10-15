import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h10, h12, h15, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h10, h12, h14, h17, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h10, h12, h19, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h10, h12, h14, h19, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h11, h12, h14, h22, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h11, h12, h24, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h10, h12, h14, h26, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h1, h10, h22, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h0, h11, h12, h28, h30, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                              · linarith only [h11, h12, h26, h30, h32, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h11, h12, h26, h28, h32, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h11, h12, h26, h28, h32, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h11, h12, h26, h28, h32, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h0, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h11, h12, h26, h28, h32, h7, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h0, h11, h12, h26, h28, h32, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht5b, p34_1, u5ehi1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h1, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h4, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h11, h12, h26, h28, h32, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h0, h11, h12, h26, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h2, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h5, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h7, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h11, h12, h26, h28, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h3, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h6, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h8, hlam, p34_0]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [h9, hlam, p34_1]
                                · have p34_0 := h34c.1
                                  have p34_1 := h34c.2.1
                                  have p34_2 := h34c.2.2.1
                                  have p34_3 := h34c.2.2.2
                                  linarith only [hlam, p34_0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                · linarith only [h11, h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                  · linarith only [h10, h11, h62, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h0, h10, h11, h5, h64, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                      · linarith only [h2, h66, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                        · linarith only [h0, h10, h11, h4, h66, h68, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                          · linarith only [h0, h10, h11, h4, h64, h66, h7, h70, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                            · linarith only [h0, h10, h11, h4, h66, h68, h7, h72, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h10, h11, h4, h7, h72, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                · linarith only [h10, h76, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h1, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                      · linarith only [h0, h10, h4, h75, h79, h8, h81, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                          · linarith only [h0, h4, h84, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h10, h4, h75, h8, h83, h84, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h10, h4, h7, h75, h83, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h10, h75, h78, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                · linarith only [h75, h89, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                    · linarith only [h1, h92, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                      · linarith only [h0, h4, h8, h91, h92, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                          · linarith only [h0, h4, h91, h92, h97, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h99 | h99
                            · linarith only [h0, h4, h8, h94, h96, h97, h99, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                              · linarith only [h101, h75, h91, h99, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h0bigk with h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h4, h7, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h7, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h0, hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h7, h75, h9, h96, h97, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h0, h101, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h0, h101, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h1, hlam, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h4, hlam, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h75, h9, h96, h97, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h0, h101, h4, h75, h9, h96, h97, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h2, hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h5, hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h7, hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h101, h75, h9, h96, h97, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h3, hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h6, hlam, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h8, hlam, p103_0]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [h9, hlam, p103_1]
                                · have p103_0 := h103c.1
                                  have p103_1 := h103c.2.1
                                  have p103_2 := h103c.2.2.1
                                  have p103_3 := h103c.2.2.2
                                  linarith only [hlam, p103_0]
                        · linarith only [h10, h91, h96, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                    · linarith only [h130, h91, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h132, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h135 | h135
                          · linarith only [h0, h130, h135, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h10, h134, h135, h91, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                          · linarith only [h0, h134, h138, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                            · linarith only [h0, h134, h140, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h142 | h142
                              · linarith only [h0, h142, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h10, h134, h142, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
            · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
              · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                · linarith only [h0, h147, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h150 | h150
                    · linarith only [h1, h150, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                      · linarith only [h152, h2, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                        · linarith only [h0, h145, h147, h154, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h145, h147, h149, h154, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                    · linarith only [h149, h157, h7, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h159 | h159
                      · linarith only [h149, h159, h2, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                        · linarith only [h145, h149, h161, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                          · linarith only [h145, h149, h157, h163, h7, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h165 | h165
                            · linarith only [h0, h146, h147, h163, h165, h4, h8, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                              · linarith only [h167, h7, h9, hc03, hlam, hphi, ht0b, ht5b, u5ehi0]
                              · rcases h0bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h146, h147, h161, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h146, h147, h161, h163, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  rcases p169_3 (m.d 0 1) (by simp) with h173 | h173
                                  · rcases p169_3 (m.d 0 2) (by simp) with h174 | h174
                                    · linarith only [h0, h174, hlam]
                                    · linarith only [h174, h5, hlam]
                                  · linarith only [h173, h2, hlam]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h146, h147, h161, h163, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h0, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h146, h147, h161, h163, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  rcases p169_3 (m.d 0 1) (by simp) with h182 | h182
                                  · rcases p169_3 (m.d 0 2) (by simp) with h183 | h183
                                    · rcases p169_3 (m.d 0 3) (by simp) with h184 | h184
                                      · linarith only [h184, h4, hlam]
                                      · linarith only [h184, h7, hlam]
                                    · linarith only [h183, h5, hlam]
                                  · linarith only [h182, h2, hlam]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h0, h146, h147, h161, h163, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h1, hlam, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h4, hlam, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  rcases p169_3 (m.d 0 1) (by simp) with h193 | h193
                                  · rcases p169_3 (m.d 0 2) (by simp) with h194 | h194
                                    · rcases p169_3 (m.d 0 3) (by simp) with h195 | h195
                                      · rcases p169_3 (m.d 0 4) (by simp) with h196 | h196
                                        · linarith only [h196, h7, hlam]
                                        · rcases p169_3 (m.d 0 5) (by simp) with h198 | h198
                                          · linarith only [h198, h8, hlam]
                                          · linarith only [h198, h9, hlam]
                                      · linarith only [h195, h7, hlam]
                                    · linarith only [h194, h5, hlam]
                                  · linarith only [h193, h2, hlam]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h0, h146, h147, h161, h163, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h2, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h5, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h7, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h9, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h3, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h6, hlam, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h8, hlam, p169_0]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [h145, h149, h7, h9, hc23, hc45, hlam, hphi, ht34, p169_1]
                                · have p169_0 := h169c.1
                                  have p169_1 := h169c.2.1
                                  have p169_2 := h169c.2.2.1
                                  have p169_3 := h169c.2.2.2
                                  linarith only [hlam, p169_0]
              · linarith only [h145, h146, h5, h9, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
              · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                · linarith only [h145, h217, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                    · linarith only [h1, h220, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h145, h216, h220, h222, h4, h8, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                          · linarith only [h0, h145, h216, h220, h224, h225, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h145, h216, h224, h225, h8, h9, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h145, h216, h224, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h145, h216, h219, h7, h9, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
                · linarith only [h216, h230, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h233 | h233
                    · linarith only [h1, h233, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h235 | h235
                      · linarith only [h2, h216, h235, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                          · linarith only [h0, h232, h233, h238, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h240 | h240
                            · linarith only [h237, h238, h240, h8, h9, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h242 | h242
                              · linarith only [h232, h242, h9, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                              · rcases h0bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h216, h237, h238, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h216, h237, h238, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  rcases p244_3 (m.d 0 1) (by simp) with h248 | h248
                                  · rcases p244_3 (m.d 0 2) (by simp) with h249 | h249
                                    · linarith only [h0, h249, hlam]
                                    · linarith only [h249, h5, hlam]
                                  · linarith only [h2, h248, hlam]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h216, h237, h238, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h0, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h216, h237, h238, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  rcases p244_3 (m.d 0 1) (by simp) with h257 | h257
                                  · rcases p244_3 (m.d 0 2) (by simp) with h258 | h258
                                    · rcases p244_3 (m.d 0 3) (by simp) with h259 | h259
                                      · linarith only [h259, h4, hlam]
                                      · linarith only [h259, h7, hlam]
                                    · linarith only [h258, h5, hlam]
                                  · linarith only [h2, h257, hlam]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h0, h216, h237, h238, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h1, hlam, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h4, hlam, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  rcases p244_3 (m.d 0 1) (by simp) with h268 | h268
                                  · rcases p244_3 (m.d 0 2) (by simp) with h269 | h269
                                    · rcases p244_3 (m.d 0 3) (by simp) with h270 | h270
                                      · rcases p244_3 (m.d 0 4) (by simp) with h271 | h271
                                        · linarith only [h271, h7, hlam]
                                        · rcases p244_3 (m.d 0 5) (by simp) with h273 | h273
                                          · linarith only [h273, h8, hlam]
                                          · linarith only [h273, h9, hlam]
                                      · linarith only [h270, h7, hlam]
                                    · linarith only [h269, h5, hlam]
                                  · linarith only [h2, h268, hlam]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h216, h237, h238, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h2, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h5, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h7, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h9, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h3, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h6, hlam, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h8, hlam, p244_0]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [h216, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p244_1]
                                · have p244_0 := h244c.1
                                  have p244_1 := h244c.2.1
                                  have p244_2 := h244c.2.2.1
                                  have p244_3 := h244c.2.2.2
                                  linarith only [hlam, p244_0]
                        · linarith only [h145, h232, h237, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
                    · linarith only [h232, h291, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                      · linarith only [h2, h293, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                          · linarith only [h0, h291, h296, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h0, h145, h232, h295, h296, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h145, h295, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h300 | h300
          · linarith only [h300, h7, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
            · rcases m.htr 1 2 4 (by decide) (by decide) with h303 | h303
              · rcases m.htr 1 2 5 (by decide) (by decide) with h304 | h304
                · linarith only [h0, h304, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                    · linarith only [h0, h302, h304, h307, h6, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                      · linarith only [h0, h300, h302, h304, h306, h309, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                        · linarith only [h0, h302, h304, h311, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h311, h7, h8, hc23, hc35, hlam, hphi]
                  · linarith only [h306, h7, h8, hc13, hc35, hlam, hphi]
              · linarith only [h302, h303, h5, h7, h8, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
              · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                · linarith only [h302, h317, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
                    · linarith only [h302, h316, h320, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
                      · linarith only [h300, h302, h316, h322, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                          · linarith only [h325, h4, h8, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
                            · linarith only [h300, h302, h316, h327, h4, h8, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                              · linarith only [h300, h302, h316, h324, h329, h4, h8, hlam]
                              · linarith only [h302, h316, h329, h4, h8, hc24, hc45, hlam, hphi]
                        · linarith only [h302, h316, h324, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h319, h7, h8, hc13, hc35, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h334 | h334
                · linarith only [h300, h316, h334, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h336 | h336
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                    · linarith only [h1, h337, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h339 | h339
                      · linarith only [h2, h300, h316, h339, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
                          · linarith only [h342, h4, h8, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                            · linarith only [h300, h344, h5, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                              · linarith only [h300, h316, h346, h5, hc12, hc34, hlam, hphi, ht23]
                              · rcases h0bigk with h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p348_1, u5ehi2]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  rcases p348_3 (m.d 0 1) (by simp) with h351 | h351
                                  · rcases p348_3 (m.d 0 2) (by simp) with h352 | h352
                                    · linarith only [h0, h352, hlam]
                                    · linarith only [h352, h4, hlam]
                                  · linarith only [h1, h351, hlam]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  rcases p348_3 (m.d 0 1) (by simp) with h356 | h356
                                  · rcases p348_3 (m.d 0 2) (by simp) with h357 | h357
                                    · linarith only [h0, h357, hlam]
                                    · linarith only [h357, h5, hlam]
                                  · linarith only [h2, h356, hlam]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h334, h6, hc01, hlam, hphi, ht0b, ht5b, p348_1, u5ehi1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h0, hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  rcases p348_3 (m.d 0 1) (by simp) with h364 | h364
                                  · rcases p348_3 (m.d 0 2) (by simp) with h365 | h365
                                    · rcases p348_3 (m.d 0 3) (by simp) with h366 | h366
                                      · linarith only [h366, h4, hlam]
                                      · rcases p348_3 (m.d 0 4) (by simp) with h368 | h368
                                        · linarith only [h368, h5, hlam]
                                        · rcases p348_3 (m.d 0 5) (by simp) with h370 | h370
                                          · linarith only [h370, h6, hlam]
                                          · linarith only [h370, h8, hlam]
                                    · linarith only [h365, h4, hlam]
                                  · linarith only [h1, h364, hlam]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  rcases p348_3 (m.d 0 1) (by simp) with h375 | h375
                                  · rcases p348_3 (m.d 0 2) (by simp) with h376 | h376
                                    · rcases p348_3 (m.d 0 3) (by simp) with h377 | h377
                                      · linarith only [h377, h4, hlam]
                                      · linarith only [h377, h7, hlam]
                                    · linarith only [h376, h5, hlam]
                                  · linarith only [h2, h375, hlam]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h0, h334, h6, hc01, hlam, hphi, ht0b, ht5b, p348_1, u5ehi1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h1, hlam, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h4, hlam, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h316, h346, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h8, hlam, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h2, hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h5, hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h7, hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h300, hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h3, hlam, p348_0]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h6, hlam, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h346, h7, h8, hc34, hc45, hlam, hphi, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [h316, h346, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p348_1]
                                · have p348_0 := h348c.1
                                  have p348_1 := h348c.2.1
                                  have p348_2 := h348c.2.2.1
                                  have p348_3 := h348c.2.2.2
                                  linarith only [hlam, p348_0]
                        · linarith only [h302, h341, h7, h8, hc13, hc35, hlam, hphi]
                  · linarith only [h302, h336, h7, h8, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
        · linarith only [h400, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h402 | h402
          · rcases m.htr 1 2 3 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 2 4 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 5 (by decide) (by decide) with h405 | h405
                · linarith only [h0, h405, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                  · linarith only [h1, h402, h407, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                    · linarith only [h1, h409, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h411 | h411
                      · linarith only [h0, h404, h405, h411, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                        · linarith only [h0, h403, h405, h413, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h415 | h415
                          · linarith only [h1, h403, h415, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                            · linarith only [h0, h404, h405, h407, h411, h417, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h402, h403, h405, h417, h7, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h420 | h420
                · linarith only [h0, h404, h420, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h422 | h422
                  · linarith only [h402, h422, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h424 | h424
                    · linarith only [h0, h403, h404, h424, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h426 | h426
                      · linarith only [h2, h426, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h402, h403, h404, h426, h7, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
              · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                · linarith only [h0, h430, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                  · linarith only [h4, h403, h432, h7, hlam]
                  · linarith only [h403, h429, h432, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
                · linarith only [h4, h403, h435, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h437 | h437
                  · linarith only [h402, h437, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h439 | h439
                    · linarith only [h1, h4, h400, h403, h439, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h441 | h441
                      · linarith only [h2, h441, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h443 | h443
                        · linarith only [h402, h443, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
                          · linarith only [h0, h443, h445, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                            · linarith only [h0, h441, h447, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · linarith only [h402, h429, h447, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
            · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
              · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
                · linarith only [h0, h452, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                  · linarith only [h1, h454, h7, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h456 | h456
                    · linarith only [h1, h400, h450, h452, h456, h6, h7, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h458 | h458
                      · linarith only [h0, h402, h451, h452, h458, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h460 | h460
                        · linarith only [h1, h450, h460, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h462 | h462
                          · linarith only [h400, h451, h452, h460, h462, h6, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h464 | h464
                            · linarith only [h402, h451, h452, h464, h6, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h466 | h466
                              · linarith only [h402, h451, h452, h460, h466, h6, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h451, h452, h460, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  rcases p468_3 (m.d 0 1) (by simp) with h471 | h471
                                  · rcases p468_3 (m.d 0 2) (by simp) with h472 | h472
                                    · linarith only [h0, h472, hlam]
                                    · linarith only [h4, h472, hlam]
                                  · linarith only [h1, h471, hlam]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  rcases p468_3 (m.d 0 1) (by simp) with h476 | h476
                                  · rcases p468_3 (m.d 0 2) (by simp) with h477 | h477
                                    · linarith only [h0, h477, hlam]
                                    · linarith only [h477, h5, hlam]
                                  · linarith only [h2, h476, hlam]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h451, h452, h460, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
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
                                  rcases p468_3 (m.d 0 1) (by simp) with h484 | h484
                                  · rcases p468_3 (m.d 0 2) (by simp) with h485 | h485
                                    · rcases p468_3 (m.d 0 3) (by simp) with h486 | h486
                                      · linarith only [h4, h486, hlam]
                                      · rcases p468_3 (m.d 0 4) (by simp) with h488 | h488
                                        · linarith only [h488, h5, hlam]
                                        · linarith only [h488, h7, hlam]
                                    · linarith only [h4, h485, hlam]
                                  · linarith only [h1, h484, hlam]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  rcases p468_3 (m.d 0 1) (by simp) with h493 | h493
                                  · rcases p468_3 (m.d 0 2) (by simp) with h494 | h494
                                    · rcases p468_3 (m.d 0 3) (by simp) with h495 | h495
                                      · linarith only [h4, h495, hlam]
                                      · rcases p468_3 (m.d 0 4) (by simp) with h497 | h497
                                        · linarith only [h497, h5, hlam]
                                        · rcases p468_3 (m.d 0 5) (by simp) with h499 | h499
                                          · linarith only [h499, h6, hlam]
                                          · linarith only [h402, h499, hlam]
                                    · linarith only [h494, h5, hlam]
                                  · linarith only [h2, h493, hlam]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h451, h452, h460, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h1, hlam, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h4, hlam, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h7, hlam, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h400, hlam, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h2, hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h5, hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h1, h466, h7, hc13, hc45, hlam, hphi, ht34, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h402, hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h3, hlam, p468_0]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [h6, hlam, p468_1]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  rcases p468_3 (m.d 0 1) (by simp) with h517 | h517
                                  · rcases p468_3 (m.d 0 2) (by simp) with h518 | h518
                                    · rcases p468_3 (m.d 0 3) (by simp) with h519 | h519
                                      · linarith only [h400, h519, hlam]
                                      · rcases p468_3 (m.d 0 4) (by simp) with h521 | h521
                                        · linarith only [h402, h521, hlam]
                                        · linarith only [h521, h7, hlam]
                                    · linarith only [h4, h518, hlam]
                                  · linarith only [h1, h517, hlam]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  rcases p468_3 (m.d 0 1) (by simp) with h526 | h526
                                  · rcases p468_3 (m.d 0 2) (by simp) with h527 | h527
                                    · rcases p468_3 (m.d 0 3) (by simp) with h528 | h528
                                      · linarith only [h400, h528, hlam]
                                      · rcases p468_3 (m.d 0 4) (by simp) with h530 | h530
                                        · linarith only [h402, h530, hlam]
                                        · rcases p468_3 (m.d 0 5) (by simp) with h532 | h532
                                          · rcases h2bigk with h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              rcases p533_3 (m.d 0 2) (by simp) with h535 | h535
                                              · rcases p533_3 (m.d 1 2) (by simp) with h536 | h536
                                                · linarith only [h0, h536, hlam]
                                                · rcases p533_3 (m.d 2 3) (by simp) with h538 | h538
                                                  · linarith only [h4, h538, hlam]
                                                  · rcases p533_3 (m.d 2 4) (by simp) with h540 | h540
                                                    · linarith only [h5, h540, hlam]
                                                    · rcases p533_3 (m.d 2 5) (by simp) with h542 | h542
                                                      · linarith only [h542, h6, hlam]
                                                      · linarith only [h452, h542, hlam]
                                              · linarith only [h0, h535, hlam]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h451, h452, h460, h6, hlam, p533_2]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h451, h452, h6, hlam, p533_2]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h451, h452, h460, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p533_1]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h0, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h0, h452, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p533_1]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h400, h452, h460, h6, hc23, hc35, hlam, hphi, p533_1]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h452, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h4, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h450, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h460, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h462, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h5, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h451, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h466, h5, h7, hc23, hc45, hlam, hphi, ht34, p533_1]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h464, hlam, p533_1]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h6, hlam, p533_0]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [h0, h450, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p533_1]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              rcases p533_3 (m.d 0 2) (by simp) with h566 | h566
                                              · rcases p533_3 (m.d 1 2) (by simp) with h567 | h567
                                                · linarith only [h452, h567, hlam]
                                                · linarith only [h450, h567, hlam]
                                              · linarith only [h4, h566, hlam]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              rcases p533_3 (m.d 0 2) (by simp) with h571 | h571
                                              · rcases p533_3 (m.d 1 2) (by simp) with h572 | h572
                                                · linarith only [h452, h572, hlam]
                                                · linarith only [h451, h572, hlam]
                                              · linarith only [h5, h571, hlam]
                                            · have p533_0 := h533c.1
                                              have p533_1 := h533c.2.1
                                              have p533_2 := h533c.2.2.1
                                              have p533_3 := h533c.2.2.2
                                              linarith only [hlam, p533_0]
                                          · linarith only [h402, h532, hlam]
                                    · linarith only [h5, h527, hlam]
                                  · linarith only [h2, h526, hlam]
                                · have p468_0 := h468c.1
                                  have p468_1 := h468c.2.1
                                  have p468_2 := h468c.2.2.1
                                  have p468_3 := h468c.2.2.2
                                  linarith only [hlam, p468_0]
              · linarith only [h402, h450, h451, h5, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h582 | h582
              · linarith only [h4, h402, h450, h582, h7, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h584 | h584
                · linarith only [h4, h402, h450, h584, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h586 | h586
                  · linarith only [h1, h4, h450, h586, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                    · linarith only [h4, h400, h450, h588, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h590 | h590
                      · linarith only [h402, h5, h582, h590, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h592 | h592
                        · linarith only [h4, h592, h7, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h594 | h594
                          · linarith only [h4, h400, h594, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h596 | h596
                            · linarith only [h402, h5, h596, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h598 | h598
                              · linarith only [h4, h402, h450, h598, h7, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h4, h450, h598, h7, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h601 | h601
      · rcases m.htr 0 3 5 (by decide) (by decide) with h602 | h602
        · linarith only [h4, h6, h602, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h604 | h604
          · linarith only [h4, h6, h601, h604, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
            · rcases m.htr 1 2 4 (by decide) (by decide) with h607 | h607
              · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
                · linarith only [h0, h6, h608, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                    · linarith only [h1, h611, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
                      · linarith only [h1, h602, h610, h613, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h615 | h615
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h616 | h616
                          · linarith only [h3, h602, h606, h608, h616, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h618 | h618
                            · linarith only [h2, h3, h604, h607, h618, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · linarith only [h0, h6, h606, h615, h618, hc34, hc45, hlam, hphi]
                        · linarith only [h601, h602, h615, hc23, hc35, hlam, hphi]
                  · linarith only [h601, h602, h606, h610, hc23, hc35, hlam, hphi]
              · linarith only [h5, h6, h607, hc12, hc25, hlam, hphi]
            · linarith only [h4, h6, h606, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h625 | h625
        · linarith only [h5, h6, h601, h625, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h627 | h627
          · linarith only [h5, h6, h627, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
            · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
              · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
                · linarith only [h0, h6, h631, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h633 | h633
                  · linarith only [h1, h601, h633, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                    · linarith only [h1, h601, h625, h635, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h637 | h637
                      · linarith only [h2, h637, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h639 | h639
                        · linarith only [h0, h1, h6, h601, h629, h639, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
                          · linarith only [h4, h6, h625, h641, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h643 | h643
                            · linarith only [h0, h6, h601, h627, h630, h641, h643, hc03, hc35, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h645 | h645
                              · linarith only [h4, h6, h643, h645, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h649 | h649
                                  · rcases p647_3 (m.d 0 2) (by simp) with h650 | h650
                                    · linarith only [h0, h650, hlam]
                                    · rcases p647_3 (m.d 0 3) (by simp) with h652 | h652
                                      · linarith only [h1, h652, hlam]
                                      · rcases p647_3 (m.d 0 4) (by simp) with h654 | h654
                                        · linarith only [h2, h654, hlam]
                                        · rcases p647_3 (m.d 0 5) (by simp) with h656 | h656
                                          · linarith only [h3, h656, hlam]
                                          · linarith only [h6, h656, hlam]
                                  · linarith only [h0, h649, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h660 | h660
                                  · rcases p647_3 (m.d 0 2) (by simp) with h661 | h661
                                    · linarith only [h0, h661, hlam]
                                    · linarith only [h4, h661, hlam]
                                  · linarith only [h1, h660, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h665 | h665
                                  · rcases p647_3 (m.d 0 2) (by simp) with h666 | h666
                                    · linarith only [h0, h666, hlam]
                                    · linarith only [h5, h666, hlam]
                                  · linarith only [h2, h665, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p647_1, u5ehi1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h0, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h1, h6, h629, h641, hc23, hc35, hlam, hphi, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h1, h6, h601, h629, h641, h645, hc23, hc45, hlam, hphi, ht34, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h6, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h1, hlam, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h4, hlam, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h601, hlam, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h625, hlam, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h2, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h5, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h1, h5, h6, h629, h641, h645, hc23, hc45, hlam, hphi, ht34, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h627, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h3, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h0, h6, h630, h641, h645, hc24, hc45, hlam, hphi, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h688 | h688
                                  · rcases p647_3 (m.d 0 2) (by simp) with h689 | h689
                                    · linarith only [h6, h689, hlam]
                                    · linarith only [h4, h689, hlam]
                                  · linarith only [h1, h688, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h693 | h693
                                  · rcases p647_3 (m.d 0 2) (by simp) with h694 | h694
                                    · linarith only [h6, h694, hlam]
                                    · linarith only [h5, h694, hlam]
                                  · linarith only [h2, h693, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
              · linarith only [h5, h6, h630, hc12, hc25, hlam, hphi]
            · linarith only [h4, h6, h629, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h701 | h701
    · linarith only [h5, h701, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h703 | h703
      · linarith only [h4, h5, h703, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h705 | h705
        · linarith only [h4, h5, h705, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h707 | h707
          · rcases m.htr 1 2 3 (by decide) (by decide) with h708 | h708
            · rcases m.htr 1 2 4 (by decide) (by decide) with h709 | h709
              · linarith only [h0, h5, h709, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h711 | h711
                · linarith only [h0, h701, h711, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h713 | h713
                  · linarith only [h1, h703, h713, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h715 | h715
                    · linarith only [h1, h705, h715, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
                      · linarith only [h2, h717, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h703, h707, h708, h709, h717, hc23, hc34, hlam, hphi]
            · linarith only [h4, h701, h708, hc12, hc25, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
            · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
              · linarith only [h0, h5, h722, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                · linarith only [h0, h5, h724, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h726 | h726
                  · linarith only [h1, h703, h726, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h728 | h728
                    · linarith only [h1, h703, h705, h728, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h730 | h730
                      · linarith only [h0, h2, h5, h707, h721, h730, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                        · linarith only [h0, h5, h707, h721, h732, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
                          · linarith only [h0, h5, h705, h707, h721, h734, hc03, hc45, hlam, hphi, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h736 | h736
                            · linarith only [h4, h5, h707, h732, h736, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h5, h721, h736, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h721, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9546000 in
set_option maxHeartbeats 9546000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h740 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h741 | h741
  · linarith only [h4, h741, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h743 | h743
    · rcases m.htr 0 3 5 (by decide) (by decide) with h744 | h744
      · rcases m.htr 0 4 5 (by decide) (by decide) with h745 | h745
        · linarith only [h4, h740, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
          · linarith only [h0, h4, h740, h747, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h749 | h749
            · rcases m.htr 1 2 5 (by decide) (by decide) with h750 | h750
              · linarith only [h0, h3, h741, h750, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                  · linarith only [h1, h753, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h755 | h755
                    · linarith only [h4, h744, h745, h747, h749, h753, h755, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h757 | h757
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h758 | h758
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h759 | h759
                          · linarith only [h4, h741, h744, h745, h747, h749, h753, h759, hc02, hc23, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h761 | h761
                            · linarith only [h4, h744, h747, h749, h753, h757, h759, h761, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                            · rcases h0bigk with h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                rcases p763_3 (m.d 0 1) (by simp) with h765 | h765
                                · rcases p763_3 (m.d 0 2) (by simp) with h766 | h766
                                  · linarith only [h0, h766, hlam]
                                  · rcases p763_3 (m.d 0 3) (by simp) with h768 | h768
                                    · linarith only [h1, h768, hlam]
                                    · linarith only [h4, h768, hlam]
                                · linarith only [h0, h765, hlam]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h744, h747, h749, h753, h757, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p763_1]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                rcases p763_3 (m.d 0 1) (by simp) with h773 | h773
                                · rcases p763_3 (m.d 0 2) (by simp) with h774 | h774
                                  · linarith only [h0, h774, hlam]
                                  · linarith only [h740, h774, hlam]
                                · linarith only [h2, h773, hlam]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h744, h747, h749, h753, h757, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p763_1]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h0, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h4, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h741, h759, hc04, hc45, hlam, hphi, p763_1]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h741, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h1, hlam, p763_1]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                rcases p763_3 (m.d 0 1) (by simp) with h785 | h785
                                · rcases p763_3 (m.d 0 2) (by simp) with h786 | h786
                                  · linarith only [h4, h786, hlam]
                                  · rcases p763_3 (m.d 0 3) (by simp) with h788 | h788
                                    · rcases p763_3 (m.d 0 4) (by simp) with h789 | h789
                                      · linarith only [h743, h789, hlam]
                                      · rcases p763_3 (m.d 0 5) (by simp) with h791 | h791
                                        · linarith only [h744, h791, hlam]
                                        · linarith only [h741, h791, hlam]
                                    · linarith only [h4, h788, hlam]
                                · linarith only [h0, h785, hlam]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                rcases p763_3 (m.d 0 1) (by simp) with h797 | h797
                                · rcases p763_3 (m.d 0 2) (by simp) with h798 | h798
                                  · linarith only [h4, h798, hlam]
                                  · linarith only [h740, h798, hlam]
                                · linarith only [h2, h797, hlam]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h744, h747, h749, h753, h757, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p763_1]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h2, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h740, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h743, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h745, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h3, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h0, h741, h749, h757, h759, hc34, hc45, hlam, hphi, p763_1]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [h744, hlam, p763_0]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                rcases p763_3 (m.d 0 1) (by simp) with h811 | h811
                                · rcases p763_3 (m.d 0 2) (by simp) with h812 | h812
                                  · linarith only [h741, h812, hlam]
                                  · linarith only [h740, h812, hlam]
                                · linarith only [h2, h811, hlam]
                              · have p763_0 := h763c.1
                                have p763_1 := h763c.2.1
                                have p763_2 := h763c.2.2.1
                                have p763_3 := h763c.2.2.2
                                linarith only [hlam, p763_0]
                        · linarith only [h4, h744, h758, hlam]
                      · linarith only [h4, h744, h747, h749, h753, h757, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h743, h745, h747, h749, h752, hc24, hc45, hlam, hphi]
            · linarith only [h740, h741, h749, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
        · linarith only [h4, h740, h744, h821, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h823 | h823
          · linarith only [h0, h4, h823, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h825 | h825
            · rcases m.htr 1 2 5 (by decide) (by decide) with h826 | h826
              · linarith only [h0, h826, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h828 | h828
                · rcases m.htr 1 3 5 (by decide) (by decide) with h829 | h829
                  · linarith only [h1, h829, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h831 | h831
                    · linarith only [h2, h821, h831, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h834 | h834
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
                          · linarith only [h0, h4, h744, h821, h825, h834, h835, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h837 | h837
                            · linarith only [h0, h4, h744, h825, h833, h834, h835, h837, hlam]
                            · rcases h0bigk with h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                rcases p839_3 (m.d 0 1) (by simp) with h841 | h841
                                · rcases p839_3 (m.d 0 2) (by simp) with h842 | h842
                                  · linarith only [h0, h842, hlam]
                                  · rcases p839_3 (m.d 0 3) (by simp) with h844 | h844
                                    · linarith only [h1, h844, hlam]
                                    · linarith only [h4, h844, hlam]
                                · linarith only [h0, h841, hlam]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                rcases p839_3 (m.d 0 1) (by simp) with h848 | h848
                                · rcases p839_3 (m.d 0 2) (by simp) with h849 | h849
                                  · linarith only [h0, h849, hlam]
                                  · rcases p839_3 (m.d 0 3) (by simp) with h851 | h851
                                    · linarith only [h1, h851, hlam]
                                    · rcases p839_3 (m.d 0 4) (by simp) with h853 | h853
                                      · linarith only [h2, h853, hlam]
                                      · rcases p839_3 (m.d 0 5) (by simp) with h855 | h855
                                        · linarith only [h3, h855, hlam]
                                        · linarith only [h744, h855, hlam]
                                · linarith only [h1, h848, hlam]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                rcases p839_3 (m.d 0 1) (by simp) with h859 | h859
                                · rcases p839_3 (m.d 0 2) (by simp) with h860 | h860
                                  · linarith only [h0, h860, hlam]
                                  · linarith only [h740, h860, hlam]
                                · linarith only [h2, h859, hlam]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p839_1, u5ehi1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h0, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h4, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h4, h744, h834, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h741, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h1, hlam, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h744, h834, hc02, hc23, hlam, hphi, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h740, h744, h833, h834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h744, hlam, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h2, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h740, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h743, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h821, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h3, hlam, p839_0]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h0, h741, h825, h833, h835, hc34, hc45, hlam, hphi, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [h0, h4, h744, h825, h833, h834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p839_1]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                rcases p839_3 (m.d 0 1) (by simp) with h883 | h883
                                · rcases p839_3 (m.d 0 2) (by simp) with h884 | h884
                                  · linarith only [h741, h884, hlam]
                                  · linarith only [h740, h884, hlam]
                                · linarith only [h2, h883, hlam]
                              · have p839_0 := h839c.1
                                have p839_1 := h839c.2.1
                                have p839_2 := h839c.2.2.1
                                have p839_3 := h839c.2.2.2
                                linarith only [hlam, p839_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h889 | h889
                          · linarith only [h0, h825, h889, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h891 | h891
                            · linarith only [h0, h4, h741, h825, h833, h834, h889, h891, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                            · linarith only [h0, h4, h825, h833, h834, h891, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h4, h743, h825, h833, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h743, h744, h828, hc13, hc35, hlam, hphi]
            · linarith only [h4, h740, h825, hc12, hc23, hlam, hphi]
    · linarith only [h4, h740, h743, hlam]

end R2N4
