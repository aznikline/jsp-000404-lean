import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h10, h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h10, h13, h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h13, h14, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h13, h19, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h10, h13, h21, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h10, h13, h23, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                            · rcases h0bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi3]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi3]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h10, h19, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h10, h19, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h0, hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h10, h19, h8, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h0, h10, h19, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h0, h10, h19, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h1, hlam, p27_1]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h4, hlam, p27_1]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h10, h19, h8, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h0, h10, h19, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h2, hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h5, hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h7, hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h10, h19, h8, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p27_1, u3ehi2]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h3, hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h6, hlam, p27_1]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h8, hlam, p27_0]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [h9, hlam, p27_1]
                              · have p27_0 := h27c.1
                                have p27_1 := h27c.2.1
                                have p27_2 := h27c.2.2.1
                                have p27_3 := h27c.2.2.2
                                linarith only [hlam, p27_0]
                            · linarith only [h0, h10, h11, h13, h25, h26, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                            · linarith only [h21, h25, h54, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h0, h10, h13, h4, h54, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
              · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                      · linarith only [h0, h10, h4, h59, h63, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h10, h59, h61, h63, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h4, h61, h62, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h10, h59, h61, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                      · linarith only [h0, h59, h6, h60, h70, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h10, h69, h70, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h4, h68, h69, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h10, h59, h68, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                        · linarith only [h0, h5, h59, h75, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h3, h59, h75, h77, h78, h79, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h10, h75, h76, h77, h78, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h76, h77, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h4, h7, h76, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h10, h75, h84, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                            · rcases h0bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h4, h75, h89, h91, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h1, h87, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p93_1, u3ehi4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h97 | h97
                                · rcases p93_3 (m.d 0 2) (by simp) with h98 | h98
                                  · linarith only [h0, h98, hlam]
                                  · linarith only [h5, h98, hlam]
                                · linarith only [h2, h97, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h102 | h102
                                · rcases p93_3 (m.d 0 2) (by simp) with h103 | h103
                                  · linarith only [h0, h103, hlam]
                                  · linarith only [h103, h6, hlam]
                                · linarith only [h102, h3, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h0, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h10, h4, h87, h92, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p93_1, u3ehi4]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h110 | h110
                                · rcases p93_3 (m.d 0 2) (by simp) with h111 | h111
                                  · rcases p93_3 (m.d 0 3) (by simp) with h112 | h112
                                    · linarith only [h112, h4, hlam]
                                    · linarith only [h112, h7, hlam]
                                  · linarith only [h111, h5, hlam]
                                · linarith only [h110, h2, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h117 | h117
                                · rcases p93_3 (m.d 0 2) (by simp) with h118 | h118
                                  · rcases p93_3 (m.d 0 3) (by simp) with h119 | h119
                                    · linarith only [h119, h4, hlam]
                                    · linarith only [h119, h8, hlam]
                                  · linarith only [h118, h6, hlam]
                                · linarith only [h117, h3, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h1, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h4, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h127 | h127
                                · rcases p93_3 (m.d 0 2) (by simp) with h128 | h128
                                  · rcases p93_3 (m.d 0 3) (by simp) with h129 | h129
                                    · rcases p93_3 (m.d 0 4) (by simp) with h130 | h130
                                      · linarith only [h130, h7, hlam]
                                      · rcases p93_3 (m.d 0 5) (by simp) with h132 | h132
                                        · linarith only [h132, h8, hlam]
                                        · rcases h2bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h4, h5, h59, hlam, p134_2, p93_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, h10, h87, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p134_1, u3ehi4]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            rcases p134_3 (m.d 0 2) (by simp) with h138 | h138
                                            · rcases p134_3 (m.d 1 2) (by simp) with h139 | h139
                                              · linarith only [h0, h139, hlam]
                                              · rcases p134_3 (m.d 2 3) (by simp) with h141 | h141
                                                · linarith only [h141, h4, hlam]
                                                · linarith only [h141, h89, hlam]
                                            · linarith only [h138, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            rcases p134_3 (m.d 0 2) (by simp) with h145 | h145
                                            · rcases p134_3 (m.d 1 2) (by simp) with h146 | h146
                                              · linarith only [h0, h146, hlam]
                                              · rcases p134_3 (m.d 2 3) (by simp) with h148 | h148
                                                · linarith only [h148, h4, hlam]
                                                · linarith only [h148, h90, hlam]
                                            · linarith only [h145, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h10, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h59, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h75, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h4, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            rcases p134_3 (m.d 0 2) (by simp) with h158 | h158
                                            · rcases p134_3 (m.d 1 2) (by simp) with h159 | h159
                                              · linarith only [h159, hlam, p134_0]
                                              · rcases p134_3 (m.d 2 3) (by simp) with h161 | h161
                                                · rcases p134_3 (m.d 2 4) (by simp) with h162 | h162
                                                  · linarith only [h162, h89, hlam]
                                                  · linarith only [h162, h59, hlam]
                                                · linarith only [h161, hlam, p134_0]
                                            · linarith only [h0, h158, hlam]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, h4, h59, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, h4, h75, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h5, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, p93_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h89, hlam, p134_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, h4, h5, h75, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p134_1, p93_1, u3ehi4]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h6, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p134_1, p93_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h90, hlam, p134_1]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [h91, hlam, p134_0]
                                          · have p134_0 := h134c.1
                                            have p134_1 := h134c.2.1
                                            have p134_2 := h134c.2.2.1
                                            have p134_3 := h134c.2.2.2
                                            linarith only [hlam, p134_0]
                                    · linarith only [h129, h7, hlam]
                                  · linarith only [h128, h5, hlam]
                                · linarith only [h127, h2, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h183 | h183
                                · rcases p93_3 (m.d 0 2) (by simp) with h184 | h184
                                  · rcases p93_3 (m.d 0 3) (by simp) with h185 | h185
                                    · rcases p93_3 (m.d 0 4) (by simp) with h186 | h186
                                      · linarith only [h186, h7, hlam]
                                      · linarith only [h186, h9, hlam]
                                    · linarith only [h185, h8, hlam]
                                  · linarith only [h184, h6, hlam]
                                · linarith only [h183, h3, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h2, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h5, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h7, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                rcases p93_3 (m.d 0 1) (by simp) with h196 | h196
                                · rcases p93_3 (m.d 0 2) (by simp) with h197 | h197
                                  · rcases p93_3 (m.d 0 3) (by simp) with h198 | h198
                                    · rcases p93_3 (m.d 0 4) (by simp) with h199 | h199
                                      · rcases p93_3 (m.d 0 5) (by simp) with h200 | h200
                                        · linarith only [h200, h9, hlam]
                                        · rcases h2bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h5, h6, h75, hlam, p202_2, p93_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, h10, h87, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u3ehi4]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            rcases p202_3 (m.d 0 2) (by simp) with h206 | h206
                                            · rcases p202_3 (m.d 1 2) (by simp) with h207 | h207
                                              · linarith only [h0, h207, hlam]
                                              · rcases p202_3 (m.d 2 3) (by simp) with h209 | h209
                                                · linarith only [h209, h4, hlam]
                                                · linarith only [h209, h89, hlam]
                                            · linarith only [h206, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            rcases p202_3 (m.d 0 2) (by simp) with h213 | h213
                                            · rcases p202_3 (m.d 1 2) (by simp) with h214 | h214
                                              · linarith only [h0, h214, hlam]
                                              · rcases p202_3 (m.d 2 3) (by simp) with h216 | h216
                                                · linarith only [h216, h4, hlam]
                                                · linarith only [h216, h90, hlam]
                                            · linarith only [h213, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h10, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h59, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h75, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h4, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            rcases p202_3 (m.d 0 2) (by simp) with h226 | h226
                                            · rcases p202_3 (m.d 1 2) (by simp) with h227 | h227
                                              · linarith only [h227, hlam, p202_0]
                                              · rcases p202_3 (m.d 2 3) (by simp) with h229 | h229
                                                · rcases p202_3 (m.d 2 4) (by simp) with h230 | h230
                                                  · linarith only [h230, h89, hlam]
                                                  · linarith only [h230, h59, hlam]
                                                · linarith only [h229, hlam, p202_0]
                                            · linarith only [h0, h226, hlam]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h59, hc12, hc23, hlam, hphi, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, h4, h75, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h5, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            rcases p202_3 (m.d 0 2) (by simp) with h239 | h239
                                            · rcases p202_3 (m.d 1 2) (by simp) with h240 | h240
                                              · linarith only [h240, hlam, p202_0]
                                              · rcases p202_3 (m.d 2 3) (by simp) with h242 | h242
                                                · rcases p202_3 (m.d 2 4) (by simp) with h243 | h243
                                                  · rcases p202_3 (m.d 2 5) (by simp) with h244 | h244
                                                    · linarith only [h244, h91, hlam]
                                                    · linarith only [h244, h75, hlam]
                                                  · linarith only [h243, hlam, p202_0]
                                                · linarith only [h10, h242, hlam]
                                            · linarith only [h0, h239, hlam]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h89, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, h5, h75, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1, u3ehi4]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h6, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p202_1, p93_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h90, hlam, p202_1]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [h91, hlam, p202_0]
                                          · have p202_0 := h202c.1
                                            have p202_1 := h202c.2.1
                                            have p202_2 := h202c.2.2.1
                                            have p202_3 := h202c.2.2.2
                                            linarith only [hlam, p202_0]
                                      · linarith only [h199, h9, hlam]
                                    · linarith only [h198, h8, hlam]
                                  · linarith only [h197, h6, hlam]
                                · linarith only [h196, h3, hlam]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h3, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h6, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h8, hlam, p93_0]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [h9, hlam, p93_1]
                              · have p93_0 := h93c.1
                                have p93_1 := h93c.2.1
                                have p93_2 := h93c.2.2.1
                                have p93_3 := h93c.2.2.2
                                linarith only [hlam, p93_0]
                            · linarith only [h0, h4, h89, h91, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                            · linarith only [h0, h268, h4, h59, h7, h91, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h0bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h10, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi1]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h59, h87, h9, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h59, h87, h9, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h0, hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h59, h8, h87, h9, h91, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h0, h59, h87, h9, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h0, h59, h87, h9, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h1, hlam, p270_1]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h4, hlam, p270_1]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h0, h4, h59, h87, h9, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h0, h4, h59, h87, h9, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h2, hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h5, hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h7, hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h59, h87, h9, h91, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1, u3ehi3]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h3, hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h6, hlam, p270_1]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h8, hlam, p270_0]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [h9, hlam, p270_1]
                              · have p270_0 := h270c.1
                                have p270_1 := h270c.2.1
                                have p270_2 := h270c.2.2.1
                                have p270_3 := h270c.2.2.2
                                linarith only [hlam, p270_0]
                        · linarith only [h10, h88, h90, hlam]
                      · linarith only [h10, h87, h89, hlam]
                    · linarith only [h87, h88, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h299 | h299
                    · linarith only [h0, h299, h4, h7, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                      · linarith only [h0, h301, h4, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                        · linarith only [h299, h301, h303, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                            · rcases h0bigk with h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c | h307c
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h301, h305, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p307_1, u3ehi3]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h10, h303, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h10, h303, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
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
                                linarith only [h10, h303, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, h10, h303, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, h10, h303, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h1, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h4, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, h10, h303, h4, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h0, h10, h303, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h2, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h5, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h7, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h10, h303, h8, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h3, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h6, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h8, hlam, p307_0]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [h9, hlam, p307_1]
                              · have p307_0 := h307c.1
                                have p307_1 := h307c.2.1
                                have p307_2 := h307c.2.2.1
                                have p307_3 := h307c.2.2.2
                                linarith only [hlam, p307_0]
                            · linarith only [h0, h306, h4, h7, h87, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                            · linarith only [h0, h305, h334, h4, h59, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h334, h87, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
            · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
              · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h0, h337, h342, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h340, h342, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h340, h341, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h340, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h0, h337, h339, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h337, h338, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
              · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                      · linarith only [h0, h337, h349, h353, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h337, h349, h351, h353, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h351, h352, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h351, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h359 | h359
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h349, h350, h360, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h358, h360, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h358, h359, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h358, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h365 | h365
                · rcases m.htr 1 3 4 (by decide) (by decide) with h366 | h366
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                    · linarith only [h349, h365, h367, h5, h9, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h366, h367, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h366, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h372 | h372
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h373 | h373
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h374 | h374
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h375 | h375
                          · linarith only [h375, h5, h9, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h377 | h377
                            · linarith only [h349, h371, h377, h5, h9, hlam]
                            · rcases h0bigk with h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c | h379c
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h337, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p379_1, u3ehi1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h1, h372, h377, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p379_1, u3ehi3]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 1) (by simp) with h383 | h383
                                · rcases p379_3 (m.d 0 2) (by simp) with h384 | h384
                                  · linarith only [h0, h384, hlam]
                                  · linarith only [h384, h5, hlam]
                                · linarith only [h2, h383, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 1) (by simp) with h388 | h388
                                · rcases p379_3 (m.d 0 2) (by simp) with h389 | h389
                                  · linarith only [h0, h389, hlam]
                                  · linarith only [h389, h6, hlam]
                                · linarith only [h3, h388, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h0, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h337, h372, h377, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p379_1, u3ehi3]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 1) (by simp) with h396 | h396
                                · rcases p379_3 (m.d 0 2) (by simp) with h397 | h397
                                  · rcases p379_3 (m.d 0 3) (by simp) with h398 | h398
                                    · linarith only [h398, h4, hlam]
                                    · linarith only [h398, h7, hlam]
                                  · linarith only [h397, h5, hlam]
                                · linarith only [h2, h396, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 1) (by simp) with h403 | h403
                                · rcases p379_3 (m.d 0 2) (by simp) with h404 | h404
                                  · rcases p379_3 (m.d 0 3) (by simp) with h405 | h405
                                    · linarith only [h4, h405, hlam]
                                    · linarith only [h405, h8, hlam]
                                  · linarith only [h404, h6, hlam]
                                · linarith only [h3, h403, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h1, hlam, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h4, hlam, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 1) (by simp) with h413 | h413
                                · rcases p379_3 (m.d 0 2) (by simp) with h414 | h414
                                  · rcases p379_3 (m.d 0 3) (by simp) with h415 | h415
                                    · rcases p379_3 (m.d 0 4) (by simp) with h416 | h416
                                      · linarith only [h416, h7, hlam]
                                      · rcases p379_3 (m.d 0 5) (by simp) with h418 | h418
                                        · linarith only [h418, h8, hlam]
                                        · linarith only [h418, h9, hlam]
                                    · linarith only [h415, h7, hlam]
                                  · linarith only [h414, h5, hlam]
                                · linarith only [h2, h413, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                rcases p379_3 (m.d 0 1) (by simp) with h424 | h424
                                · rcases p379_3 (m.d 0 2) (by simp) with h425 | h425
                                  · rcases p379_3 (m.d 0 3) (by simp) with h426 | h426
                                    · rcases p379_3 (m.d 0 4) (by simp) with h427 | h427
                                      · linarith only [h427, h7, hlam]
                                      · rcases p379_3 (m.d 0 5) (by simp) with h429 | h429
                                        · linarith only [h429, h8, hlam]
                                        · rcases h2bigk with h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c | h431c
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h349, h375, h4, h6, hlam, p379_1, p431_2]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h337, h372, h377, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p431_1, u3ehi3]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            rcases p431_3 (m.d 0 2) (by simp) with h435 | h435
                                            · rcases p431_3 (m.d 1 2) (by simp) with h436 | h436
                                              · linarith only [h0, h436, hlam]
                                              · rcases p431_3 (m.d 2 3) (by simp) with h438 | h438
                                                · linarith only [h4, h438, hlam]
                                                · linarith only [h373, h438, hlam]
                                            · linarith only [h435, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            rcases p431_3 (m.d 0 2) (by simp) with h442 | h442
                                            · rcases p431_3 (m.d 1 2) (by simp) with h443 | h443
                                              · linarith only [h0, h443, hlam]
                                              · rcases p431_3 (m.d 2 3) (by simp) with h445 | h445
                                                · linarith only [h4, h445, hlam]
                                                · linarith only [h374, h445, hlam]
                                            · linarith only [h442, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h0, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h337, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h349, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h365, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h4, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            rcases p431_3 (m.d 0 2) (by simp) with h455 | h455
                                            · rcases p431_3 (m.d 1 2) (by simp) with h456 | h456
                                              · linarith only [h456, hlam, p431_0]
                                              · rcases p431_3 (m.d 2 3) (by simp) with h458 | h458
                                                · rcases p431_3 (m.d 2 4) (by simp) with h459 | h459
                                                  · linarith only [h373, h459, hlam]
                                                  · linarith only [h349, h459, hlam]
                                                · linarith only [h458, hlam, p431_0]
                                            · linarith only [h0, h455, hlam]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h0, h349, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h0, h365, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h5, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h373, hlam, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h375, hlam, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h6, hlam, p431_0]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p379_1, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h374, hlam, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p379_1, p431_1]
                                          · have p431_0 := h431c.1
                                            have p431_1 := h431c.2.1
                                            have p431_2 := h431c.2.2.1
                                            have p431_3 := h431c.2.2.2
                                            linarith only [hlam, p431_0]
                                    · linarith only [h426, h8, hlam]
                                  · linarith only [h425, h6, hlam]
                                · linarith only [h3, h424, hlam]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h5, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h7, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h9, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h3, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h6, hlam, p379_1]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h8, hlam, p379_0]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [h2, h371, h9, hc45, hlam, hphi, ht34, p379_1, u3ehi3]
                              · have p379_0 := h379c.1
                                have p379_1 := h379c.2.1
                                have p379_2 := h379c.2.2.1
                                have p379_3 := h379c.2.2.2
                                linarith only [hlam, p379_0]
                        · linarith only [h1, h372, h374, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h337, h372, h373, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h371, h372, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h371, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h495 | h495
        · linarith only [h495, h7, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h497 | h497
          · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
            · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
              · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                  · linarith only [h1, h501, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
                    · linarith only [h1, h495, h503, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
                      · linarith only [h1, h498, h505, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h507 | h507
                        · linarith only [h1, h495, h498, h507, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                            · rcases h0bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p511_1, u3ehi2]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                rcases p511_3 (m.d 0 1) (by simp) with h514 | h514
                                · rcases p511_3 (m.d 0 2) (by simp) with h515 | h515
                                  · linarith only [h0, h515, hlam]
                                  · linarith only [h4, h515, hlam]
                                · linarith only [h1, h514, hlam]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                rcases p511_3 (m.d 0 1) (by simp) with h519 | h519
                                · rcases p511_3 (m.d 0 2) (by simp) with h520 | h520
                                  · linarith only [h0, h520, hlam]
                                  · linarith only [h5, h520, hlam]
                                · linarith only [h2, h519, hlam]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                rcases p511_3 (m.d 0 1) (by simp) with h524 | h524
                                · rcases p511_3 (m.d 0 2) (by simp) with h525 | h525
                                  · linarith only [h0, h525, hlam]
                                  · linarith only [h525, h6, hlam]
                                · linarith only [h3, h524, hlam]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h0, hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                rcases p511_3 (m.d 0 1) (by simp) with h531 | h531
                                · rcases p511_3 (m.d 0 2) (by simp) with h532 | h532
                                  · rcases p511_3 (m.d 0 3) (by simp) with h533 | h533
                                    · linarith only [h4, h533, hlam]
                                    · rcases p511_3 (m.d 0 4) (by simp) with h535 | h535
                                      · linarith only [h5, h535, hlam]
                                      · linarith only [h535, h7, hlam]
                                  · linarith only [h4, h532, hlam]
                                · linarith only [h1, h531, hlam]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                rcases p511_3 (m.d 0 1) (by simp) with h540 | h540
                                · rcases p511_3 (m.d 0 2) (by simp) with h541 | h541
                                  · rcases p511_3 (m.d 0 3) (by simp) with h542 | h542
                                    · linarith only [h4, h542, hlam]
                                    · rcases p511_3 (m.d 0 4) (by simp) with h544 | h544
                                      · linarith only [h5, h544, hlam]
                                      · rcases p511_3 (m.d 0 5) (by simp) with h546 | h546
                                        · linarith only [h546, h6, hlam]
                                        · rcases h2bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h499, h507, h509, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            rcases p548_3 (m.d 0 2) (by simp) with h551 | h551
                                            · rcases p548_3 (m.d 1 2) (by simp) with h552 | h552
                                              · linarith only [h0, h552, hlam]
                                              · linarith only [h498, h552, hlam]
                                            · linarith only [h551, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            rcases p548_3 (m.d 0 2) (by simp) with h556 | h556
                                            · rcases p548_3 (m.d 1 2) (by simp) with h557 | h557
                                              · linarith only [h0, h557, hlam]
                                              · linarith only [h499, h557, hlam]
                                            · linarith only [h556, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            rcases p548_3 (m.d 0 2) (by simp) with h561 | h561
                                            · rcases p548_3 (m.d 1 2) (by simp) with h562 | h562
                                              · linarith only [h0, h562, hlam]
                                              · linarith only [h500, h562, hlam]
                                            · linarith only [h561, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h0, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h0, h507, h509, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h0, h507, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h4, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h498, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h505, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h507, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h5, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h499, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h2, h499, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h0, h2, h499, h507, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p511_1, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h6, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h500, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1, u3ehi2]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [h509, hlam, p548_0]
                                          · have p548_0 := h548c.1
                                            have p548_1 := h548c.2.1
                                            have p548_2 := h548c.2.2.1
                                            have p548_3 := h548c.2.2.2
                                            linarith only [hlam, p548_0]
                                  · linarith only [h5, h541, hlam]
                                · linarith only [h2, h540, hlam]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                rcases p511_3 (m.d 0 1) (by simp) with h588 | h588
                                · rcases p511_3 (m.d 0 2) (by simp) with h589 | h589
                                  · rcases p511_3 (m.d 0 3) (by simp) with h590 | h590
                                    · linarith only [h4, h590, hlam]
                                    · rcases p511_3 (m.d 0 4) (by simp) with h592 | h592
                                      · linarith only [h5, h592, hlam]
                                      · linarith only [h497, h592, hlam]
                                  · linarith only [h589, h6, hlam]
                                · linarith only [h3, h588, hlam]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h1, hlam, p511_1]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h4, hlam, p511_1]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h7, hlam, p511_1]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h495, hlam, p511_1]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h2, hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h5, hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h1, h498, h7, hc34, hlam, hphi, p511_1, u3ehi2]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h1, h495, h498, h7, hc34, hlam, hphi, p511_1, u3ehi2]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h3, hlam, p511_0]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h6, hlam, p511_1]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h1, h495, h498, hc35, hlam, hphi, p511_1, u3ehi2]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [h497, hlam, p511_1]
                              · have p511_0 := h511c.1
                                have p511_1 := h511c.2.1
                                have p511_2 := h511c.2.2.1
                                have p511_3 := h511c.2.2.2
                                linarith only [hlam, p511_0]
                            · linarith only [h0, h499, h509, h510, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h497, h505, h509, h7, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h498, h500, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h498, h499, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h616 | h616
              · rcases m.htr 1 2 5 (by decide) (by decide) with h617 | h617
                · rcases m.htr 1 3 4 (by decide) (by decide) with h618 | h618
                  · linarith only [h4, h498, h618, h7, hlam]
                  · linarith only [h4, h498, h616, h618, h7, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                  · linarith only [h4, h498, h616, h621, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h4, h498, h616, h621, h7, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
                · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                  · linarith only [h4, h498, h624, h625, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h627 | h627
                    · linarith only [h1, h627, h7, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h4, h498, h624, h627, h7, hc34, hlam, hphi, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h630 | h630
                  · linarith only [h1, h4, h498, h630, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h632 | h632
                    · linarith only [h4, h495, h498, h616, h630, h632, hc12, hc24, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                      · linarith only [h4, h634, h7, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                        · linarith only [h4, h495, h636, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h639 | h639
                            · rcases h0bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h4, h498, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h643 | h643
                                · rcases p640_3 (m.d 0 2) (by simp) with h644 | h644
                                  · linarith only [h0, h644, hlam]
                                  · linarith only [h4, h644, hlam]
                                · linarith only [h1, h643, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h648 | h648
                                · rcases p640_3 (m.d 0 2) (by simp) with h649 | h649
                                  · linarith only [h0, h649, hlam]
                                  · linarith only [h5, h649, hlam]
                                · linarith only [h2, h648, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h653 | h653
                                · rcases p640_3 (m.d 0 2) (by simp) with h654 | h654
                                  · linarith only [h0, h654, hlam]
                                  · linarith only [h6, h654, hlam]
                                · linarith only [h3, h653, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h0, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h660 | h660
                                · rcases p640_3 (m.d 0 2) (by simp) with h661 | h661
                                  · rcases p640_3 (m.d 0 3) (by simp) with h662 | h662
                                    · linarith only [h4, h662, hlam]
                                    · rcases p640_3 (m.d 0 4) (by simp) with h664 | h664
                                      · linarith only [h5, h664, hlam]
                                      · linarith only [h664, h7, hlam]
                                  · linarith only [h4, h661, hlam]
                                · linarith only [h1, h660, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h669 | h669
                                · rcases p640_3 (m.d 0 2) (by simp) with h670 | h670
                                  · rcases p640_3 (m.d 0 3) (by simp) with h671 | h671
                                    · linarith only [h4, h671, hlam]
                                    · rcases p640_3 (m.d 0 4) (by simp) with h673 | h673
                                      · linarith only [h5, h673, hlam]
                                      · rcases p640_3 (m.d 0 5) (by simp) with h675 | h675
                                        · linarith only [h6, h675, hlam]
                                        · rcases h2bigk with h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h4, h498, h7, hlam, p640_1, p677_2]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            rcases p677_3 (m.d 0 2) (by simp) with h680 | h680
                                            · rcases p677_3 (m.d 1 2) (by simp) with h681 | h681
                                              · linarith only [h0, h681, hlam]
                                              · rcases p677_3 (m.d 2 3) (by simp) with h683 | h683
                                                · linarith only [h683, hlam, p677_0]
                                                · rcases p677_3 (m.d 2 4) (by simp) with h685 | h685
                                                  · linarith only [h5, h685, hlam]
                                                  · linarith only [h634, h685, hlam]
                                            · linarith only [h680, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            rcases p677_3 (m.d 0 2) (by simp) with h689 | h689
                                            · rcases p677_3 (m.d 1 2) (by simp) with h690 | h690
                                              · linarith only [h0, h690, hlam]
                                              · rcases p677_3 (m.d 2 3) (by simp) with h692 | h692
                                                · linarith only [h4, h692, hlam]
                                                · rcases p677_3 (m.d 2 4) (by simp) with h694 | h694
                                                  · linarith only [h694, hlam, p677_0]
                                                  · rcases p677_3 (m.d 2 5) (by simp) with h696 | h696
                                                    · linarith only [h6, h696, hlam]
                                                    · rcases h3bigk with h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c | h698c
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h495, h497, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1, p698_1, u3ehi1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h495, h497, h498, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, p698_1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h7, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h495, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h1, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h498, hlam, p698_1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h630, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h632, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h4, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p698_1, u3ehi1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h634, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h636, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hc34, hlam, hphi, p698_1, u3ehi0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hc34, hlam, hphi, p698_1, u3ehi1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h498, hc12, hc34, hlam, hphi, ht23, p698_1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h4, h495, h498, hc12, hc34, hlam, hphi, ht23, p698_1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h4, h498, hc12, hc35, hlam, hphi, ht23, p698_1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hc35, hlam, hphi, p698_1, u3ehi1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h498, hc12, hc35, hlam, hphi, ht23, p698_1]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [h639, hlam, p698_0]
                                                      · have p698_0 := h698c.1
                                                        have p698_1 := h698c.2.1
                                                        have p698_2 := h698c.2.2.1
                                                        have p698_3 := h698c.2.2.2
                                                        linarith only [hlam, p698_0]
                                            · linarith only [h689, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            rcases p677_3 (m.d 0 2) (by simp) with h725 | h725
                                            · rcases p677_3 (m.d 1 2) (by simp) with h726 | h726
                                              · linarith only [h0, h726, hlam]
                                              · rcases p677_3 (m.d 2 3) (by simp) with h728 | h728
                                                · linarith only [h4, h728, hlam]
                                                · rcases p677_3 (m.d 2 4) (by simp) with h730 | h730
                                                  · linarith only [h5, h730, hlam]
                                                  · linarith only [h638, h730, hlam]
                                            · linarith only [h725, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h0, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h498, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h616, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h624, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h4, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p677_1]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h634, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h636, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h5, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, p677_1]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1, p677_1, u3ehi2]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h0, h5, h624, h632, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1, p677_1, u3ehi1]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h6, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h0, h497, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, p677_1]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h0, h497, h498, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, p677_1]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [h638, hlam, p677_0]
                                          · have p677_0 := h677c.1
                                            have p677_1 := h677c.2.1
                                            have p677_2 := h677c.2.2.1
                                            have p677_3 := h677c.2.2.2
                                            linarith only [hlam, p677_0]
                                  · linarith only [h5, h670, hlam]
                                · linarith only [h2, h669, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                rcases p640_3 (m.d 0 1) (by simp) with h756 | h756
                                · rcases p640_3 (m.d 0 2) (by simp) with h757 | h757
                                  · rcases p640_3 (m.d 0 3) (by simp) with h758 | h758
                                    · linarith only [h4, h758, hlam]
                                    · rcases p640_3 (m.d 0 4) (by simp) with h760 | h760
                                      · linarith only [h5, h760, hlam]
                                      · linarith only [h497, h760, hlam]
                                  · linarith only [h6, h757, hlam]
                                · linarith only [h3, h756, hlam]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h1, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h4, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h7, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h495, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h2, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h5, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h4, h498, h7, hc12, hc34, hlam, hphi, ht23, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h3, h632, h7, hc34, hlam, hphi, p640_1, u3ehi1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h3, hlam, p640_0]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h6, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h4, h495, h498, h639, hc12, hc34, hlam, hphi, ht23, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [h497, hlam, p640_1]
                              · have p640_0 := h640c.1
                                have p640_1 := h640c.2.1
                                have p640_2 := h640c.2.2.1
                                have p640_3 := h640c.2.2.2
                                linarith only [hlam, p640_0]
                            · linarith only [h0, h5, h638, h639, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h497, h616, h638, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
            · rcases m.htr 1 2 4 (by decide) (by decide) with h783 | h783
              · rcases m.htr 1 2 5 (by decide) (by decide) with h784 | h784
                · rcases m.htr 1 3 4 (by decide) (by decide) with h785 | h785
                  · linarith only [h1, h7, h785, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h787 | h787
                    · linarith only [h1, h495, h787, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
                      · linarith only [h7, h782, h789, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h791 | h791
                        · linarith only [h1, h495, h782, h791, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h793 | h793
                          · linarith only [h0, h1, h497, h5, h7, h782, h793, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h795 | h795
                            · linarith only [h1, h497, h7, h782, h795, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1, h7, h782, h795, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h6, h782, h784, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h5, h782, h783, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
              · linarith only [h4, h497, h7, h782, h800, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h802 | h802
                · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                  · linarith only [h4, h7, h782, h803, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h805 | h805
                    · linarith only [h4, h495, h782, h802, h805, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h4, h497, h7, h782, h802, h805, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                  · linarith only [h1, h4, h7, h782, h808, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                    · linarith only [h4, h495, h782, h810, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h812 | h812
                      · linarith only [h4, h7, h812, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h814 | h814
                        · linarith only [h4, h495, h814, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h816 | h816
                          · linarith only [h497, h5, h816, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                            · linarith only [h4, h497, h7, h782, h818, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h4, h7, h782, h818, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h821 | h821
      · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
        · linarith only [h4, h6, h822, hlam]
        · linarith only [h821, h822, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h825 | h825
        · linarith only [h821, h825, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h827 | h827
          · linarith only [h5, h6, h827, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h829 | h829
            · rcases m.htr 1 2 4 (by decide) (by decide) with h830 | h830
              · rcases m.htr 1 2 5 (by decide) (by decide) with h831 | h831
                · linarith only [h0, h6, h831, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
                  · linarith only [h1, h821, h833, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h835 | h835
                    · linarith only [h0, h1, h6, h821, h825, h829, h835, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                      · linarith only [h0, h6, h829, h837, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h839 | h839
                        · linarith only [h0, h6, h825, h830, h837, h839, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h4, h6, h839, hc35, hlam, hphi, u3ehi2]
              · linarith only [h5, h6, h829, h830, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h4, h6, h829, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h844 | h844
    · rcases m.htr 0 3 4 (by decide) (by decide) with h845 | h845
      · linarith only [h4, h5, h845, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h847 | h847
        · linarith only [h845, h847, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h849 | h849
          · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
            · rcases m.htr 1 2 4 (by decide) (by decide) with h851 | h851
              · linarith only [h0, h5, h844, h847, h851, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
                · rcases m.htr 1 3 4 (by decide) (by decide) with h854 | h854
                  · linarith only [h0, h1, h5, h845, h847, h850, h854, hc35, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
                    · linarith only [h1, h847, h856, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h858 | h858
                      · linarith only [h0, h5, h845, h850, h858, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h4, h5, h858, hc34, hlam, hphi, u3ehi2]
                · linarith only [h844, h850, h853, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h4, h5, h850, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h849, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h864 | h864
      · linarith only [h4, h5, h864, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h866 | h866
        · linarith only [h864, h866, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h868 | h868
          · rcases m.htr 1 2 3 (by decide) (by decide) with h869 | h869
            · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
              · linarith only [h0, h5, h870, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
                · linarith only [h0, h844, h872, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h874 | h874
                  · linarith only [h1, h864, h874, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h876 | h876
                    · linarith only [h1, h866, h876, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h878 | h878
                      · linarith only [h0, h864, h869, h878, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h5, h869, h878, hc34, hlam, hphi, u3ehi2]
            · linarith only [h4, h5, h869, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h868, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
