import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
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
                        · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h16, h20, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                          · linarith only [h0, h11, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h10, h13, h16, h22, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h10, h13, h15, h16, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                        · linarith only [h0, h10, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h14, h27, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                        · linarith only [h0, h27, h31, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                          · linarith only [h13, h15, h27, h33, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                            · linarith only [h13, h15, h35, hlam]
                            · rcases h2bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi2]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h13, h15, h27, h4, h7, h9, hlam, p37_2]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                rcases p37_3 (m.d 0 2) (by simp) with h41 | h41
                                · rcases p37_3 (m.d 1 2) (by simp) with h42 | h42
                                  · linarith only [h0, h42, hlam]
                                  · linarith only [h11, h42, hlam]
                                · linarith only [h41, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                rcases p37_3 (m.d 0 2) (by simp) with h46 | h46
                                · rcases p37_3 (m.d 1 2) (by simp) with h47 | h47
                                  · linarith only [h0, h47, hlam]
                                  · linarith only [h12, h47, hlam]
                                · linarith only [h46, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h0, hlam, p37_1]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                rcases p37_3 (m.d 0 2) (by simp) with h53 | h53
                                · rcases p37_3 (m.d 1 2) (by simp) with h54 | h54
                                  · rcases p37_3 (m.d 2 3) (by simp) with h55 | h55
                                    · linarith only [h55, hlam, p37_0]
                                    · rcases p37_3 (m.d 2 4) (by simp) with h57 | h57
                                      · linarith only [h11, h57, hlam]
                                      · linarith only [h27, h57, hlam]
                                  · linarith only [h54, hlam, p37_0]
                                · linarith only [h4, h53, hlam]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                rcases p37_3 (m.d 0 2) (by simp) with h62 | h62
                                · rcases p37_3 (m.d 1 2) (by simp) with h63 | h63
                                  · rcases p37_3 (m.d 2 3) (by simp) with h64 | h64
                                    · linarith only [h10, h64, hlam]
                                    · rcases p37_3 (m.d 2 4) (by simp) with h66 | h66
                                      · linarith only [h66, hlam, p37_0]
                                      · rcases p37_3 (m.d 2 5) (by simp) with h68 | h68
                                        · linarith only [h12, h68, hlam]
                                        · linarith only [h33, h68, hlam]
                                  · linarith only [h63, hlam, p37_0]
                                · linarith only [h5, h62, hlam]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi2]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h4, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h10, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h27, hlam, p37_1]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h31, hlam, p37_1]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h5, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h11, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h33, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h6, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h12, hlam, p37_0]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [h1, h14, h31, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                              · have p37_0 := h37c.1
                                have p37_1 := h37c.2.1
                                have p37_2 := h37c.2.2.1
                                have p37_3 := h37c.2.2.2
                                linarith only [hlam, p37_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h13, h14, h4, h8, h89, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h10, h14, h92, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h94 | h94
                          · linarith only [h0, h11, h89, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h89, h96, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                            · rcases h2bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h10, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h101 | h101
                                · rcases p98_3 (m.d 1 2) (by simp) with h102 | h102
                                  · linarith only [h0, h102, hlam]
                                  · linarith only [h10, h102, hlam]
                                · linarith only [h101, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h106 | h106
                                · rcases p98_3 (m.d 1 2) (by simp) with h107 | h107
                                  · linarith only [h0, h107, hlam]
                                  · linarith only [h107, h11, hlam]
                                · linarith only [h106, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h111 | h111
                                · rcases p98_3 (m.d 1 2) (by simp) with h112 | h112
                                  · linarith only [h0, h112, hlam]
                                  · linarith only [h112, h12, hlam]
                                · linarith only [h111, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                rcases p98_3 (m.d 0 2) (by simp) with h119 | h119
                                · rcases p98_3 (m.d 1 2) (by simp) with h120 | h120
                                  · rcases p98_3 (m.d 2 3) (by simp) with h121 | h121
                                    · linarith only [h10, h121, hlam]
                                    · linarith only [h121, h91, hlam]
                                  · linarith only [h120, hlam, p98_0]
                                · linarith only [h119, h5, hlam]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h91, h92, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h4, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h10, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h92, hlam, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h5, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h11, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h91, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h94, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h6, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h12, hlam, p98_0]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [h0, h12, h91, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                              · have p98_0 := h98c.1
                                have p98_1 := h98c.2.1
                                have p98_2 := h98c.2.2.1
                                have p98_3 := h98c.2.2.2
                                linarith only [hlam, p98_0]
                      · linarith only [h13, h14, h91, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h143 | h143
                  · linarith only [h0, h13, h143, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                      · linarith only [h13, h146, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                        · linarith only [h10, h143, h148, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                          · linarith only [h0, h11, h150, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h152 | h152
                            · rcases h2bigk with h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h0, h11, h145, h146, h150, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h13, h145, h146, h150, h4, h7, hlam, p153_2]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h13, h145, h150, h4, h7, hlam, p153_2]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                rcases p153_3 (m.d 0 2) (by simp) with h158 | h158
                                · rcases p153_3 (m.d 1 2) (by simp) with h159 | h159
                                  · linarith only [h0, h159, hlam]
                                  · linarith only [h12, h159, hlam]
                                · linarith only [h158, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h0, hlam, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                rcases p153_3 (m.d 0 2) (by simp) with h165 | h165
                                · rcases p153_3 (m.d 1 2) (by simp) with h166 | h166
                                  · rcases p153_3 (m.d 2 3) (by simp) with h167 | h167
                                    · linarith only [h167, hlam, p153_0]
                                    · rcases p153_3 (m.d 2 4) (by simp) with h169 | h169
                                      · linarith only [h11, h169, hlam]
                                      · linarith only [h146, h169, hlam]
                                  · linarith only [h166, hlam, p153_0]
                                · linarith only [h165, h4, hlam]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                rcases p153_3 (m.d 0 2) (by simp) with h174 | h174
                                · rcases p153_3 (m.d 1 2) (by simp) with h175 | h175
                                  · rcases p153_3 (m.d 2 3) (by simp) with h176 | h176
                                    · linarith only [h10, h176, hlam]
                                    · rcases p153_3 (m.d 2 4) (by simp) with h178 | h178
                                      · linarith only [h178, hlam, p153_0]
                                      · rcases p153_3 (m.d 2 5) (by simp) with h180 | h180
                                        · linarith only [h12, h180, hlam]
                                        · linarith only [h150, h180, hlam]
                                  · linarith only [h175, hlam, p153_0]
                                · linarith only [h174, h5, hlam]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p153_1, u5ehi2]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h4, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h10, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h146, hlam, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h148, hlam, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h5, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h11, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h0, h13, h145, h150, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h150, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h6, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h12, hlam, p153_0]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [h0, h13, h145, h150, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p153_1]
                              · have p153_0 := h153c.1
                                have p153_1 := h153c.2.1
                                have p153_2 := h153c.2.2.1
                                have p153_3 := h153c.2.2.2
                                linarith only [hlam, p153_0]
                            · linarith only [h13, h145, h152, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h202 | h202
                      · linarith only [h13, h202, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                        · linarith only [h143, h204, hc23, hlam, hphi, ht12, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                          · linarith only [h11, h145, h206, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                            · linarith only [h13, h145, h208, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                            · linarith only [h0, h13, h208, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 3 5 (by decide) (by decide) with h212 | h212
                  · linarith only [h0, h10, h12, h212, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h214 | h214
                    · linarith only [h0, h11, h12, h214, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                      · linarith only [h0, h10, h12, h216, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h10, h12, h211, h216, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h219 | h219
                  · linarith only [h0, h11, h12, h211, h219, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                    · linarith only [h0, h11, h12, h221, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                      · linarith only [h211, h223, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                        · linarith only [h0, h11, h12, h219, h223, h225, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h0, h11, h12, h225, h227, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                            · linarith only [h11, h12, h223, h227, h229, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h211, h229, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
              · linarith only [h0, h11, h232, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                · linarith only [h10, h11, h234, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h0, h10, h11, h236, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                      · linarith only [h234, h239, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                        · linarith only [h0, h10, h11, h236, h239, h241, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h244 | h244
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
                                rcases p245_3 (m.d 0 2) (by simp) with h247 | h247
                                · rcases p245_3 (m.d 1 2) (by simp) with h248 | h248
                                  · linarith only [h0, h248, hlam]
                                  · rcases p245_3 (m.d 2 3) (by simp) with h250 | h250
                                    · linarith only [h250, h4, hlam]
                                    · rcases p245_3 (m.d 2 4) (by simp) with h252 | h252
                                      · linarith only [h252, h5, hlam]
                                      · linarith only [h11, h252, hlam]
                                · linarith only [h0, h247, hlam]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h10, h232, h239, h243, h4, h7, hlam, p245_2]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h0, h10, h232, h243, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p245_1]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h0, h232, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p245_1, u1ehi1]
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
                                linarith only [h232, h241, hc23, hc35, hlam, hphi, p245_1]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h11, hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h232, hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h4, hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h10, hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h239, hlam, p245_1]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h241, hlam, p245_1]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h5, hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p245_1, u1ehi1]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                rcases p245_3 (m.d 0 2) (by simp) with h271 | h271
                                · rcases p245_3 (m.d 1 2) (by simp) with h272 | h272
                                  · linarith only [h11, h272, hlam]
                                  · linarith only [h10, h272, hlam]
                                · linarith only [h271, h4, hlam]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h0, h239, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p245_1, u5ehi2]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h6, hlam, p245_0]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h10, hc25, hlam, hphi, ht12, p245_1, u1ehi2]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                rcases p245_3 (m.d 0 2) (by simp) with h280 | h280
                                · rcases p245_3 (m.d 1 2) (by simp) with h281 | h281
                                  · linarith only [h232, h281, hlam]
                                  · linarith only [h10, h281, hlam]
                                · linarith only [h280, h4, hlam]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [h243, hlam, p245_1]
                              · have p245_0 := h245c.1
                                have p245_1 := h245c.2.1
                                have p245_2 := h245c.2.2.1
                                have p245_3 := h245c.2.2.2
                                linarith only [hlam, p245_0]
                            · linarith only [h10, h11, h238, h239, h244, hc14, hlam, hphi, u1ehi2]
                          · linarith only [h11, h238, h243, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                      · linarith only [h0, h10, h11, h289, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                        · linarith only [h0, h10, h11, h238, h291, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                          · linarith only [h10, h11, h238, h289, h293, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h10, h11, h293, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
            · rcases m.htr 1 2 5 (by decide) (by decide) with h297 | h297
              · linarith only [h0, h10, h297, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h299 | h299
                · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                    · linarith only [h0, h10, h296, h301, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h0, h296, h297, h301, h304, h305, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                            · linarith only [h296, h297, h303, h305, h307, hlam]
                            · rcases h2bigk with h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                rcases p309_3 (m.d 0 2) (by simp) with h311 | h311
                                · rcases p309_3 (m.d 1 2) (by simp) with h312 | h312
                                  · linarith only [h0, h312, hlam]
                                  · rcases p309_3 (m.d 2 3) (by simp) with h314 | h314
                                    · linarith only [h314, h4, hlam]
                                    · linarith only [h10, h314, hlam]
                                · linarith only [h0, h311, hlam]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h0, h10, h296, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p309_1]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h10, h296, h4, hlam, p309_2]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h0, h296, h297, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p309_1]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h0, hlam, p309_1]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h10, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h0, h297, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p309_1]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h297, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h4, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p309_1, u1ehi1]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                rcases p309_3 (m.d 0 2) (by simp) with h329 | h329
                                · rcases p309_3 (m.d 1 2) (by simp) with h330 | h330
                                  · linarith only [h10, h330, hlam]
                                  · linarith only [h296, h330, hlam]
                                · linarith only [h329, h5, hlam]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p309_1, u5ehi2]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h5, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h296, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h303, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h305, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h6, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h296, hc25, hlam, hphi, ht12, p309_1, u1ehi3]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [h304, hlam, p309_0]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                rcases p309_3 (m.d 0 2) (by simp) with h343 | h343
                                · rcases p309_3 (m.d 1 2) (by simp) with h344 | h344
                                  · linarith only [h297, h344, hlam]
                                  · linarith only [h296, h344, hlam]
                                · linarith only [h343, h5, hlam]
                              · have p309_0 := h309c.1
                                have p309_1 := h309c.2.1
                                have p309_2 := h309c.2.2.1
                                have p309_3 := h309c.2.2.2
                                linarith only [hlam, p309_0]
                        · linarith only [h10, h296, h300, h304, hc13, hlam, hphi, u1ehi3]
                      · linarith only [h0, h10, h300, h303, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h351 | h351
                    · linarith only [h0, h10, h296, h351, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                        · linarith only [h0, h10, h300, h354, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · linarith only [h0, h10, h296, h354, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                      · linarith only [h10, h296, h353, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h10, h296, h299, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
              · linarith only [h0, h10, h359, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                            · linarith only [h1, h361, h367, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases h2bigk with h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                rcases p369_3 (m.d 0 2) (by simp) with h371 | h371
                                · rcases p369_3 (m.d 1 2) (by simp) with h372 | h372
                                  · linarith only [h0, h372, hlam]
                                  · rcases p369_3 (m.d 2 3) (by simp) with h374 | h374
                                    · linarith only [h374, h4, hlam]
                                    · linarith only [h10, h374, hlam]
                                · linarith only [h0, h371, hlam]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h359, h364, h366, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h359, h366, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h359, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, hlam, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h10, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h296, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h359, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h4, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hc23, hlam, hphi, ht12, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h359, h366, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h359, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h5, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hc24, hlam, hphi, ht12, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h364, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h0, h359, h364, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h6, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hc25, hlam, hphi, ht12, p369_1, u1ehi1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h365, hlam, p369_0]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [h366, hlam, p369_1]
                              · have p369_0 := h369c.1
                                have p369_1 := h369c.2.1
                                have p369_2 := h369c.2.2.1
                                have p369_3 := h369c.2.2.2
                                linarith only [hlam, p369_0]
                          · linarith only [h296, h363, h366, hc14, hlam, hphi, u1ehi1]
                        · linarith only [h0, h10, h361, h363, h365, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h10, h364, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h405 | h405
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                          · linarith only [h363, h404, h406, hc23, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h0, h296, h4, h406, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · linarith only [h10, h362, h405, hc13, hlam, hphi, u1ehi1]
                      · linarith only [h10, h2, h361, h362, h404, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h411 | h411
                    · linarith only [h0, h361, h362, h4, h411, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                        · linarith only [h0, h361, h362, h4, h414, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h10, h414, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h10, h413, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h0, h361, h4, h418, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                      · linarith only [h361, h421, hc23, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h0, h10, h4, h421, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                      · linarith only [h0, h10, h361, h4, h424, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                      · linarith only [h10, h424, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
          · rcases m.htr 1 2 4 (by decide) (by decide) with h428 | h428
            · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
              · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
                    · linarith only [h2, h432, h9, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                        · linarith only [h0, h427, h435, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h431, h434, h435, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h438 | h438
                        · linarith only [h0, h4, h434, h438, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h440 | h440
                          · linarith only [h0, h427, h430, h434, h440, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h442 | h442
                            · linarith only [h0, h2, h427, h430, h442, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                            · rcases h2bigk with h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c | h444c
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h0, h427, h431, h434, h442, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                rcases p444_3 (m.d 0 2) (by simp) with h447 | h447
                                · rcases p444_3 (m.d 1 2) (by simp) with h448 | h448
                                  · linarith only [h0, h448, hlam]
                                  · linarith only [h427, h448, hlam]
                                · linarith only [h447, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                rcases p444_3 (m.d 0 2) (by simp) with h452 | h452
                                · rcases p444_3 (m.d 1 2) (by simp) with h453 | h453
                                  · linarith only [h0, h453, hlam]
                                  · linarith only [h428, h453, hlam]
                                · linarith only [h452, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                rcases p444_3 (m.d 0 2) (by simp) with h457 | h457
                                · rcases p444_3 (m.d 1 2) (by simp) with h458 | h458
                                  · linarith only [h0, h458, hlam]
                                  · linarith only [h429, h458, hlam]
                                · linarith only [h457, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h0, hlam, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                rcases p444_3 (m.d 0 2) (by simp) with h464 | h464
                                · rcases p444_3 (m.d 1 2) (by simp) with h465 | h465
                                  · rcases p444_3 (m.d 2 3) (by simp) with h466 | h466
                                    · linarith only [h466, hlam, p444_0]
                                    · rcases p444_3 (m.d 2 4) (by simp) with h468 | h468
                                      · linarith only [h428, h468, hlam]
                                      · linarith only [h434, h468, hlam]
                                  · linarith only [h465, hlam, p444_0]
                                · linarith only [h4, h464, hlam]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                rcases p444_3 (m.d 0 2) (by simp) with h473 | h473
                                · rcases p444_3 (m.d 1 2) (by simp) with h474 | h474
                                  · rcases p444_3 (m.d 2 3) (by simp) with h475 | h475
                                    · linarith only [h427, h475, hlam]
                                    · rcases p444_3 (m.d 2 4) (by simp) with h477 | h477
                                      · linarith only [h477, hlam, p444_0]
                                      · rcases p444_3 (m.d 2 5) (by simp) with h479 | h479
                                        · linarith only [h429, h479, hlam]
                                        · linarith only [h440, h479, hlam]
                                  · linarith only [h474, hlam, p444_0]
                                · linarith only [h473, h5, hlam]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p444_1, u5ehi2]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h4, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h427, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h434, hlam, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h438, hlam, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h5, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h428, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h440, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h6, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h429, hlam, p444_0]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h0, h429, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [h1, h431, h438, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p444_1]
                              · have p444_0 := h444c.1
                                have p444_1 := h444c.2.1
                                have p444_2 := h444c.2.2.1
                                have p444_3 := h444c.2.2.2
                                linarith only [hlam, p444_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
                    · linarith only [h4, h430, h431, h500, h8, h9, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h502 | h502
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h503 | h503
                        · linarith only [h430, h431, h503, hc23, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h505 | h505
                          · linarith only [h430, h431, h505, h8, h9, hc24, hlam, hphi, ht12, u1ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                            · linarith only [h430, h431, h507, h8, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                            · rcases h2bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h427, h502, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 2) (by simp) with h512 | h512
                                · rcases p509_3 (m.d 1 2) (by simp) with h513 | h513
                                  · linarith only [h0, h513, hlam]
                                  · linarith only [h427, h513, hlam]
                                · linarith only [h512, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 2) (by simp) with h517 | h517
                                · rcases p509_3 (m.d 1 2) (by simp) with h518 | h518
                                  · linarith only [h0, h518, hlam]
                                  · linarith only [h428, h518, hlam]
                                · linarith only [h517, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 2) (by simp) with h522 | h522
                                · rcases p509_3 (m.d 1 2) (by simp) with h523 | h523
                                  · linarith only [h0, h523, hlam]
                                  · linarith only [h429, h523, hlam]
                                · linarith only [h522, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, hlam, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h502, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                rcases p509_3 (m.d 0 2) (by simp) with h530 | h530
                                · rcases p509_3 (m.d 1 2) (by simp) with h531 | h531
                                  · rcases p509_3 (m.d 2 3) (by simp) with h532 | h532
                                    · linarith only [h427, h532, hlam]
                                    · linarith only [h502, h532, hlam]
                                  · linarith only [h531, hlam, p509_0]
                                · linarith only [h5, h530, hlam]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h502, h503, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h4, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h427, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h427, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h503, hlam, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h5, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h428, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h502, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h505, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h6, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h429, hlam, p509_0]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h429, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [h0, h429, h502, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p509_1]
                              · have p509_0 := h509c.1
                                have p509_1 := h509c.2.1
                                have p509_2 := h509c.2.2.1
                                have p509_3 := h509c.2.2.2
                                linarith only [hlam, p509_0]
                      · linarith only [h0, h4, h430, h431, h502, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h430, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                · rcases m.htr 1 3 5 (by decide) (by decide) with h556 | h556
                  · linarith only [h0, h427, h429, h556, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h558 | h558
                    · linarith only [h0, h427, h429, h555, h558, h6, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
                      · linarith only [h0, h427, h429, h560, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h427, h429, h555, h560, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h555, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · linarith only [h427, h428, h5, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h565 | h565
            · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
              · linarith only [h0, h4, h427, h566, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h570 | h570
                    · linarith only [h0, h4, h427, h565, h570, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h573 | h573
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h574 | h574
                          · linarith only [h565, h566, h574, h6, h9, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h576 | h576
                            · linarith only [h565, h566, h572, h576, h6, h9, hlam]
                            · rcases h2bigk with h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                rcases p578_3 (m.d 0 2) (by simp) with h580 | h580
                                · rcases p578_3 (m.d 1 2) (by simp) with h581 | h581
                                  · linarith only [h0, h581, hlam]
                                  · rcases p578_3 (m.d 2 3) (by simp) with h583 | h583
                                    · linarith only [h4, h583, hlam]
                                    · linarith only [h427, h583, hlam]
                                · linarith only [h0, h580, hlam]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h0, h565, h566, h573, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p578_1, u1ehi3]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h4, h565, h566, h573, hlam, p578_2]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h565, h566, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p578_1, u1ehi3]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h0, hlam, p578_1]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h427, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h566, h572, h6, h9, hc34, hc45, hlam, hphi, p578_1]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h566, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h4, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p578_1, u1ehi1]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                rcases p578_3 (m.d 0 2) (by simp) with h598 | h598
                                · rcases p578_3 (m.d 1 2) (by simp) with h599 | h599
                                  · linarith only [h427, h599, hlam]
                                  · linarith only [h565, h599, hlam]
                                · linarith only [h5, h598, hlam]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p578_1, u5ehi2]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h5, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h565, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h572, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h574, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h6, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h565, hc25, hlam, hphi, ht12, p578_1, u1ehi3]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [h573, hlam, p578_0]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                rcases p578_3 (m.d 0 2) (by simp) with h612 | h612
                                · rcases p578_3 (m.d 1 2) (by simp) with h613 | h613
                                  · linarith only [h566, h613, hlam]
                                  · linarith only [h565, h613, hlam]
                                · linarith only [h5, h612, hlam]
                              · have p578_0 := h578c.1
                                have p578_1 := h578c.2.1
                                have p578_2 := h578c.2.2.1
                                have p578_3 := h578c.2.2.2
                                linarith only [hlam, p578_0]
                        · linarith only [h427, h565, h569, h573, hc13, hlam, hphi, u1ehi3]
                      · linarith only [h0, h4, h427, h569, h572, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
                    · linarith only [h2, h620, h9, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h623 | h623
                        · linarith only [h0, h4, h427, h569, h623, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · linarith only [h427, h565, h623, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h427, h565, h622, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h427, h565, h568, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
            · linarith only [h5, h565, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h629 | h629
        · linarith only [h629, h7, h8, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h631 | h631
          · rcases m.htr 1 2 4 (by decide) (by decide) with h632 | h632
            · rcases m.htr 1 2 5 (by decide) (by decide) with h633 | h633
              · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                  · linarith only [h1, h635, h8, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h637 | h637
                    · linarith only [h2, h629, h637, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h639 | h639
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h640 | h640
                        · linarith only [h0, h631, h640, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
                          · linarith only [h2, h3, h629, h632, h642, h7, h8, hc35, hlam, hphi, ht12, ht23, u1ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h644 | h644
                            · linarith only [h2, h629, h644, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                            · rcases h2bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h631, h639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h649 | h649
                                · rcases p646_3 (m.d 1 2) (by simp) with h650 | h650
                                  · linarith only [h0, h650, hlam]
                                  · linarith only [h631, h650, hlam]
                                · linarith only [h649, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h654 | h654
                                · rcases p646_3 (m.d 1 2) (by simp) with h655 | h655
                                  · linarith only [h0, h655, hlam]
                                  · linarith only [h632, h655, hlam]
                                · linarith only [h654, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h659 | h659
                                · rcases p646_3 (m.d 1 2) (by simp) with h660 | h660
                                  · linarith only [h0, h660, hlam]
                                  · linarith only [h633, h660, hlam]
                                · linarith only [h659, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, hlam, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                rcases p646_3 (m.d 0 2) (by simp) with h667 | h667
                                · rcases p646_3 (m.d 1 2) (by simp) with h668 | h668
                                  · rcases p646_3 (m.d 2 3) (by simp) with h669 | h669
                                    · linarith only [h631, h669, hlam]
                                    · linarith only [h639, h669, hlam]
                                  · linarith only [h668, hlam, p646_0]
                                · linarith only [h5, h667, hlam]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h639, h640, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h4, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h631, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h4, h644, h8, hc24, hc45, hlam, hphi, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h640, hlam, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h5, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h632, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h639, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h642, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h6, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h633, hlam, p646_0]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h633, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [h0, h633, h639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p646_1]
                              · have p646_0 := h646c.1
                                have p646_1 := h646c.2.1
                                have p646_2 := h646c.2.2.1
                                have p646_3 := h646c.2.2.2
                                linarith only [hlam, p646_0]
                      · linarith only [h639, h7, h8, hc23, hc35, hlam, hphi]
                · linarith only [h634, h7, h8, hc13, hc35, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h692 | h692
                · rcases m.htr 1 3 5 (by decide) (by decide) with h693 | h693
                  · linarith only [h6, h631, h633, h693, h8, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h695 | h695
                    · linarith only [h2, h629, h695, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h697 | h697
                      · linarith only [h0, h6, h631, h633, h697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h697, h7, h8, hc23, hc35, hlam, hphi]
                · linarith only [h692, h7, h8, hc13, hc35, hlam, hphi]
            · linarith only [h5, h629, h632, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
          · linarith only [h4, h631, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h703 | h703
      · rcases m.htr 0 4 5 (by decide) (by decide) with h704 | h704
        · rcases m.htr 1 2 3 (by decide) (by decide) with h705 | h705
          · rcases m.htr 1 2 4 (by decide) (by decide) with h706 | h706
            · rcases m.htr 1 2 5 (by decide) (by decide) with h707 | h707
              · rcases m.htr 1 3 4 (by decide) (by decide) with h708 | h708
                · linarith only [h7, h703, h708, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h710 | h710
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h711 | h711
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h712 | h712
                      · linarith only [h7, h703, h705, h712, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
                        · linarith only [h0, h706, h712, h714, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · linarith only [h1, h7, h710, h714, hc23, hc34, hlam, hphi]
                    · linarith only [h704, h708, h710, h711, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h7, h703, h710, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · linarith only [h6, h7, h703, h707, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h720 | h720
              · linarith only [h0, h5, h706, h720, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h6, h7, h703, h720, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h4, h7, h705, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h7, h703, h704, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h725 | h725
        · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
          · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
              · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                · linarith only [h1, h7, h729, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h731 | h731
                  · linarith only [h1, h703, h731, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h733 | h733
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h734 | h734
                      · linarith only [h1, h7, h734, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h736 | h736
                        · linarith only [h1, h703, h727, h734, h736, hc12, hlam, hphi, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h738 | h738
                          · linarith only [h0, h727, h738, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h740 | h740
                            · rcases h2bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h0, h727, h733, h734, h738, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                rcases p741_3 (m.d 0 2) (by simp) with h744 | h744
                                · rcases p741_3 (m.d 1 2) (by simp) with h745 | h745
                                  · linarith only [h0, h745, hlam]
                                  · linarith only [h726, h745, hlam]
                                · linarith only [h744, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                rcases p741_3 (m.d 0 2) (by simp) with h749 | h749
                                · rcases p741_3 (m.d 1 2) (by simp) with h750 | h750
                                  · linarith only [h0, h750, hlam]
                                  · linarith only [h727, h750, hlam]
                                · linarith only [h749, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                rcases p741_3 (m.d 0 2) (by simp) with h754 | h754
                                · rcases p741_3 (m.d 1 2) (by simp) with h755 | h755
                                  · linarith only [h0, h755, hlam]
                                  · linarith only [h728, h755, hlam]
                                · linarith only [h754, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h0, hlam, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                rcases p741_3 (m.d 0 2) (by simp) with h761 | h761
                                · rcases p741_3 (m.d 1 2) (by simp) with h762 | h762
                                  · rcases p741_3 (m.d 2 3) (by simp) with h763 | h763
                                    · linarith only [h763, hlam, p741_0]
                                    · rcases p741_3 (m.d 2 4) (by simp) with h765 | h765
                                      · linarith only [h727, h765, hlam]
                                      · linarith only [h734, h765, hlam]
                                  · linarith only [h762, hlam, p741_0]
                                · linarith only [h4, h761, hlam]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                rcases p741_3 (m.d 0 2) (by simp) with h770 | h770
                                · rcases p741_3 (m.d 1 2) (by simp) with h771 | h771
                                  · rcases p741_3 (m.d 2 3) (by simp) with h772 | h772
                                    · linarith only [h726, h772, hlam]
                                    · rcases p741_3 (m.d 2 4) (by simp) with h774 | h774
                                      · linarith only [h774, hlam, p741_0]
                                      · rcases p741_3 (m.d 2 5) (by simp) with h776 | h776
                                        · linarith only [h728, h776, hlam]
                                        · linarith only [h738, h776, hlam]
                                  · linarith only [h771, hlam, p741_0]
                                · linarith only [h5, h770, hlam]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p741_1, u5ehi2]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h4, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h726, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h734, hlam, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h736, hlam, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h5, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h727, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h2, h733, h738, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h738, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h6, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h728, hlam, p741_0]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h0, h728, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [h0, h727, h733, h738, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p741_1]
                              · have p741_0 := h741c.1
                                have p741_1 := h741c.2.1
                                have p741_2 := h741c.2.2.1
                                have p741_3 := h741c.2.2.2
                                linarith only [hlam, p741_0]
                            · linarith only [h2, h7, h733, h740, hlam]
                    · linarith only [h7, h725, h733, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h799 | h799
                · linarith only [h1, h7, h725, h799, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h801 | h801
                  · linarith only [h1, h703, h801, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h803 | h803
                    · linarith only [h0, h6, h727, h728, h803, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h7, h725, h799, h803, hc34, hlam, hphi, ht12, ht23, u1ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
              · linarith only [h0, h5, h727, h806, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                · linarith only [h1, h7, h725, h808, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h810 | h810
                  · linarith only [h0, h5, h703, h726, h727, h810, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h812 | h812
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h813 | h813
                      · linarith only [h6, h7, h725, h806, h813, hc23, hlam, hphi, ht12, u1ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h815 | h815
                        · linarith only [h6, h703, h726, h806, h815, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                            · rcases h2bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                rcases p819_3 (m.d 0 2) (by simp) with h821 | h821
                                · rcases p819_3 (m.d 1 2) (by simp) with h822 | h822
                                  · linarith only [h0, h822, hlam]
                                  · rcases p819_3 (m.d 2 3) (by simp) with h824 | h824
                                    · linarith only [h4, h824, hlam]
                                    · rcases p819_3 (m.d 2 4) (by simp) with h826 | h826
                                      · linarith only [h5, h826, hlam]
                                      · linarith only [h727, h826, hlam]
                                · linarith only [h0, h821, hlam]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h5, h726, h806, h817, hlam, p819_2]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h0, h726, h806, h817, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi2]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h0, h726, h806, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi2]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h0, hlam, p819_1]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h6, h7, h725, h806, hc23, hc34, hlam, hphi, p819_1]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h727, hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h806, hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h4, hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h726, hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h813, hlam, p819_1]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h815, hlam, p819_1]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h5, hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h0, h5, h726, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p819_1, u1ehi2]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                rcases p819_3 (m.d 0 2) (by simp) with h845 | h845
                                · rcases p819_3 (m.d 1 2) (by simp) with h846 | h846
                                  · linarith only [h727, h846, hlam]
                                  · linarith only [h726, h846, hlam]
                                · linarith only [h4, h845, hlam]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, p819_1, u5ehi2]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h6, hlam, p819_0]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h726, hc25, hlam, hphi, ht12, p819_1, u1ehi2]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                rcases p819_3 (m.d 0 2) (by simp) with h854 | h854
                                · rcases p819_3 (m.d 1 2) (by simp) with h855 | h855
                                  · linarith only [h806, h855, hlam]
                                  · linarith only [h726, h855, hlam]
                                · linarith only [h4, h854, hlam]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [h817, hlam, p819_1]
                              · have p819_0 := h819c.1
                                have p819_1 := h819c.2.1
                                have p819_2 := h819c.2.2.1
                                have p819_3 := h819c.2.2.2
                                linarith only [hlam, p819_0]
                            · linarith only [h2, h7, h725, h812, h818, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                          · linarith only [h727, h812, h817, hlam]
                    · linarith only [h7, h725, h812, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · linarith only [h4, h7, h726, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
          · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
            · rcases m.htr 1 2 5 (by decide) (by decide) with h867 | h867
              · rcases m.htr 1 3 4 (by decide) (by decide) with h868 | h868
                · linarith only [h1, h7, h868, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h870 | h870
                  · linarith only [h1, h703, h870, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h872 | h872
                    · linarith only [h2, h725, h872, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h874 | h874
                      · linarith only [h1, h7, h865, h874, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h876 | h876
                        · linarith only [h1, h703, h865, h876, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h878 | h878
                          · linarith only [h1, h7, h725, h866, h878, hc14, hlam, hphi, u1ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h880 | h880
                            · linarith only [h1, h7, h725, h880, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                            · linarith only [h1, h7, h880, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h883 | h883
                · linarith only [h1, h7, h883, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h885 | h885
                  · linarith only [h6, h703, h866, h867, h883, h885, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                    · linarith only [h0, h6, h866, h867, h887, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                      · linarith only [h0, h1, h6, h7, h865, h867, h889, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                        · linarith only [h6, h703, h866, h867, h889, h891, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                          · linarith only [h6, h725, h866, h867, h893, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                            · linarith only [h6, h725, h866, h867, h889, h895, hc23, hc34, hlam, hphi]
                            · linarith only [h1, h7, h895, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · linarith only [h5, h725, h866, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
          · linarith only [h4, h7, h865, hc34, hlam, hphi, ht12, ht23, u1ehi1]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h900 | h900
    · rcases m.htr 0 3 5 (by decide) (by decide) with h901 | h901
      · linarith only [h4, h6, h901, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h903 | h903
        · linarith only [h4, h6, h900, h903, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
          · rcases m.htr 1 2 4 (by decide) (by decide) with h906 | h906
            · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
              · linarith only [h0, h4, h6, h900, h907, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
                · rcases m.htr 1 3 5 (by decide) (by decide) with h910 | h910
                  · linarith only [h2, h900, h901, h910, hc13, hlam, hphi, u1ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h912 | h912
                    · linarith only [h2, h903, h912, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
                        · linarith only [h0, h2, h6, h900, h901, h905, h915, hc25, hlam, hphi, ht12, u1ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                          · linarith only [h2, h903, h917, hc24, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h0, h6, h905, h914, h917, hc34, hc45, hlam, hphi]
                      · linarith only [h900, h901, h914, hc23, hc35, hlam, hphi]
                · linarith only [h900, h901, h909, hc13, hc35, hlam, hphi]
            · linarith only [h5, h6, h906, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h905, hc25, hlam, hphi, ht12, u1ehi1]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
      · linarith only [h4, h6, h924, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
        · linarith only [h5, h6, h926, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h928 | h928
          · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
            · rcases m.htr 1 2 5 (by decide) (by decide) with h930 | h930
              · linarith only [h0, h6, h930, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                · linarith only [h1, h900, h932, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h934 | h934
                  · linarith only [h1, h924, h934, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h936 | h936
                    · linarith only [h2, h926, h936, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h938 | h938
                      · linarith only [h0, h1, h6, h900, h928, h938, hc25, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                        · linarith only [h0, h1, h6, h924, h929, h938, h940, hc25, hlam, hphi, ht12, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h942 | h942
                          · linarith only [h0, h1, h6, h900, h926, h929, h940, h942, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h944 | h944
                            · linarith only [h0, h6, h929, h938, h942, h944, hc23, hc34, hlam, hphi]
                            · linarith only [h1, h900, h944, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · linarith only [h5, h6, h929, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h928, hc25, hlam, hphi, ht12, u1ehi1]

end R2N4
