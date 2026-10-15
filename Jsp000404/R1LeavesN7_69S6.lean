import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_25_L_R_L_R_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                    · linarith only [h0, h10, h15, h18, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h10, h15, h17, h18, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h10, h12, h14, h17, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h10, h13, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h10, h12, h15, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                  · linarith only [h14, h24, h26, hc23, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                    · linarith only [h0, h10, h14, h24, h28, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                    · rcases h5bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p30_1, u1ehi4]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi4]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        rcases p30_3 (m.d 0 5) (by simp) with h34 | h34
                                        · rcases p30_3 (m.d 1 5) (by simp) with h35 | h35
                                          · linarith only [h3, h35, hlam]
                                          · linarith only [h13, h35, hlam]
                                        · linarith only [h34, h8, hlam]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h14, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p30_1, u1ehi3]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h3, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h26, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h10, h13, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h14, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h6, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h11, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h28, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h26, hlam, p30_0]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h8, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h13, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h25, hlam, p30_0]
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
                                        linarith only [h9, hlam, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hc15, hlam, hphi, ht0b, ht5b, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [h0, h28, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                      · have p30_0 := h30c.1
                                        have p30_1 := h30c.2.1
                                        have p30_2 := h30c.2.2.1
                                        have p30_3 := h30c.2.2.2
                                        linarith only [hlam, p30_0]
                                · linarith only [h0, h10, h13, h25, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h10, h12, h24, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                            · linarith only [h12, h13, h62, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                                · linarith only [h13, h65, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                                  · linarith only [h62, h67, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                                    · linarith only [h0, h10, h13, h4, h62, h64, h69, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                    · rcases h5bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h10, h13, h4, h64, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h4, h64, h65, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h10, h13, h4, h64, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h4, h62, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p71_1, u1ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h3, hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h64, h65, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h13, hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h62, hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h6, hlam, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h11, hlam, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h65, hlam, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h67, hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h8, hlam, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h4, h64, h65, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h69, hlam, p71_0]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h9, hlam, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h12, h13, hc45, hlam, hphi, ht12, ht23, ht34, p71_1, u1ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h4, h64, h65, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi3]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p71_1]
                                      · have p71_0 := h71c.1
                                        have p71_1 := h71c.2.1
                                        have p71_2 := h71c.2.2.1
                                        have p71_3 := h71c.2.2.2
                                        linarith only [hlam, p71_0]
                              · linarith only [h12, h13, h64, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                              · linarith only [h100, h12, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                                    · rcases h5bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [hlam, p105_0]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p105_1, u1ehi4]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi4]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        rcases p105_3 (m.d 0 5) (by simp) with h109 | h109
                                        · rcases p105_3 (m.d 1 5) (by simp) with h110 | h110
                                          · linarith only [h110, h3, hlam]
                                          · linarith only [h110, h98, hlam]
                                        · linarith only [h109, h8, hlam]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        rcases p105_3 (m.d 0 5) (by simp) with h114 | h114
                                        · rcases p105_3 (m.d 1 5) (by simp) with h115 | h115
                                          · linarith only [h115, h3, hlam]
                                          · linarith only [h115, h99, hlam]
                                        · linarith only [h114, h9, hlam]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h3, hlam, p105_0]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [hlam, p105_0]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi4]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h12, h4, h7, h98, hc01, hc35, hlam, hphi, ht0b, ht5b, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h12, h4, h7, h98, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h6, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h11, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [hlam, p105_0]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h104, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h11, h12, h4, h7, h98, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h8, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h98, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h102, hlam, p105_0]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [hlam, p105_0]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h9, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h99, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h103, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [h104, hlam, p105_1]
                                      · have p105_0 := h105c.1
                                        have p105_1 := h105c.2.1
                                        have p105_2 := h105c.2.2.1
                                        have p105_3 := h105c.2.2.2
                                        linarith only [hlam, p105_0]
                                    · linarith only [h104, h12, h98, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                                  · linarith only [h100, h103, h2, h99, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h102, h12, h4, h7, h98, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h12, h98, h99, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                              · linarith only [h10, h12, h144, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h146 | h146
                                · linarith only [h10, h146, h98, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
                                    · rcases h5bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h4, h7, h9, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p150_1, u1ehi2]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h146, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u2ehi2]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h4, h7, h9, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p150_1, u1ehi2]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        rcases p150_3 (m.d 0 5) (by simp) with h155 | h155
                                        · rcases p150_3 (m.d 1 5) (by simp) with h156 | h156
                                          · linarith only [h156, h3, hlam]
                                          · linarith only [h143, h156, hlam]
                                        · linarith only [h155, h9, hlam]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h3, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h143, h146, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p150_1, u2ehi2]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h98, hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h12, h143, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h6, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h11, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h146, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h148, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h8, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h149, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h149, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h0, h149, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h9, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h143, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h148, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [h149, hlam, p150_1]
                                      · have p150_0 := h150c.1
                                        have p150_1 := h150c.2.1
                                        have p150_2 := h150c.2.2.1
                                        have p150_3 := h150c.2.2.2
                                        linarith only [hlam, p150_0]
                                    · linarith only [h0, h12, h149, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                  · linarith only [h143, h148, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                              · linarith only [h12, h182, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                                · linarith only [h10, h184, h98, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h186 | h186
                                  · linarith only [h12, h143, h186, hc24, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                                    · linarith only [h0, h12, h143, h188, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                    · linarith only [h0, h12, h188, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · linarith only [h0, h10, h11, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                      · linarith only [h10, h192, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h195 | h195
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h199 | h199
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h200 | h200
                                    · rcases h5bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h0, h192, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi4]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        rcases p201_3 (m.d 0 5) (by simp) with h205 | h205
                                        · rcases p201_3 (m.d 1 5) (by simp) with h206 | h206
                                          · linarith only [h206, h3, hlam]
                                          · linarith only [h195, h206, hlam]
                                        · linarith only [h205, h8, hlam]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        rcases p201_3 (m.d 0 5) (by simp) with h210 | h210
                                        · rcases p201_3 (m.d 1 5) (by simp) with h211 | h211
                                          · linarith only [h211, h3, hlam]
                                          · linarith only [h196, h211, hlam]
                                        · linarith only [h210, h9, hlam]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h3, hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h192, hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h196, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h1, h194, h196, hc01, hc45, hlam, hphi, ht0b, ht5b, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h6, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h0, h198, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h0, h197, h199, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h8, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h195, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h198, hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [hlam, p201_0]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h9, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h196, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h199, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [h200, hlam, p201_1]
                                      · have p201_0 := h201c.1
                                        have p201_1 := h201c.2.1
                                        have p201_2 := h201c.2.2.1
                                        have p201_3 := h201c.2.2.2
                                        linarith only [hlam, p201_0]
                                    · rcases h5bigk with h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h0, h192, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p235_1, u1ehi1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p235_1, u2ehi4]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        rcases p235_3 (m.d 0 5) (by simp) with h239 | h239
                                        · rcases p235_3 (m.d 1 5) (by simp) with h240 | h240
                                          · linarith only [h240, h3, hlam]
                                          · linarith only [h195, h240, hlam]
                                        · linarith only [h239, h8, hlam]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h0, h200, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h3, hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h192, hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h200, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h6, hlam, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht12, p235_1, u1ehi4]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h0, h198, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h0, h197, h199, h200, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h8, hlam, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h195, hlam, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h198, hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h200, hlam, p235_0]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h9, hlam, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h196, hlam, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h199, hlam, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p235_1]
                                      · have p235_0 := h235c.1
                                        have p235_1 := h235c.2.1
                                        have p235_2 := h235c.2.2.1
                                        have p235_3 := h235c.2.2.2
                                        linarith only [hlam, p235_0]
                                  · linarith only [h0, h10, h194, h196, h199, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h10, h198, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h10, h197, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                                  · linarith only [h196, h270, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h272 | h272
                                    · linarith only [h270, h272, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h5bigk with h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c | h274c
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h192, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p274_1, u1ehi1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h192, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p274_1, u1ehi1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        rcases p274_3 (m.d 0 5) (by simp) with h278 | h278
                                        · rcases p274_3 (m.d 1 5) (by simp) with h279 | h279
                                          · linarith only [h279, h3, hlam]
                                          · linarith only [h195, h279, hlam]
                                        · linarith only [h278, h8, hlam]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h192, h270, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p274_1, u1ehi1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h3, hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h192, hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h272, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h196, hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h6, hlam, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h269, hc23, hlam, hphi, ht12, p274_1, u1ehi4]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h269, h272, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h270, hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h8, hlam, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h195, hlam, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h269, hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h272, hlam, p274_0]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h9, hlam, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h192, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p274_1, u1ehi1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [h0, h272, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p274_1]
                                      · have p274_0 := h274c.1
                                        have p274_1 := h274c.2.1
                                        have p274_2 := h274c.2.2.1
                                        have p274_3 := h274c.2.2.2
                                        linarith only [hlam, p274_0]
                                · linarith only [h0, h10, h269, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h10, h268, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h306 | h306
                            · linarith only [h194, h195, h306, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                                · linarith only [h195, h309, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h0, h10, h309, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h10, h194, h195, h308, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                              · linarith only [h194, h315, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h10, h315, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h194, h313, h314, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                              · linarith only [h194, h320, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h10, h320, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                              · linarith only [h194, h323, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h10, h323, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h327 | h327
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h329 | h329
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h330 | h330
                            · linarith only [h2, h330, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h334 | h334
                                  · linarith only [h2, h334, h9, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h336 | h336
                                    · linarith only [h2, h326, h332, h336, h9, hc12, hlam, hphi, u1ehi3]
                                    · rcases h5bigk with h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c | h338c
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, p338_1, u1ehi4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h9, hc45, hlam, hphi, ht23, ht34, p338_1, u2ehi4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h336, h9, hc34, hc45, hlam, hphi, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h9, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h3, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p338_1, u2ehi4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h0, h326, h329, h336, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h330, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h6, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h327, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h0, h336, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h334, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h8, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h329, hlam, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h333, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h336, hlam, p338_0]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, p338_1, u1ehi4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p338_1, u1ehi4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p338_1, u2ehi4]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [h336, hc34, hc45, hlam, hphi, p338_1]
                                      · have p338_0 := h338c.1
                                        have p338_1 := h338c.2.1
                                        have p338_2 := h338c.2.2.1
                                        have p338_3 := h338c.2.2.2
                                        linarith only [hlam, p338_0]
                                · linarith only [h0, h326, h329, h333, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h332, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h366 | h366
                            · linarith only [h2, h366, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h369 | h369
                                · linarith only [h329, h369, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h371 | h371
                                  · linarith only [h328, h329, h371, h8, h9, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h373 | h373
                                    · linarith only [h326, h329, h368, h373, h8, h9, hlam]
                                    · rcases h5bigk with h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h328, h329, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p375_1, u1ehi3]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h9, hc45, hlam, hphi, ht23, ht34, p375_1, u2ehi4]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h328, h329, h9, hc45, hlam, hphi, ht12, ht23, ht34, p375_1, u1ehi3]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h9, hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h3, hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p375_1, u2ehi4]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h329, hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h366, hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h6, hlam, p375_1]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h327, hlam, p375_1]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h369, hlam, p375_1]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h371, hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h8, hlam, p375_1]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p375_1]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p375_1, u2ehi4]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h373, hlam, p375_0]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h3, h328, h329, hc45, hlam, hphi, ht12, ht23, ht34, p375_1, u1ehi3]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h328, h329, hc45, hlam, hphi, ht12, ht23, ht34, p375_1, u1ehi3]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h369, hc23, hc45, hlam, hphi, ht34, p375_1]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [h328, h329, hc45, hlam, hphi, ht12, ht23, ht34, p375_1, u1ehi3]
                                      · have p375_0 := h375c.1
                                        have p375_1 := h375c.2.1
                                        have p375_2 := h375c.2.2.1
                                        have p375_3 := h375c.2.2.2
                                        linarith only [hlam, p375_0]
                              · linarith only [h368, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h328, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h0, h326, h327, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                      · linarith only [h326, h404, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h407 | h407
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                            · linarith only [h2, h408, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h411 | h411
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h412 | h412
                                  · linarith only [h404, h412, h6, h9, hc24, hlam, hphi, u2ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                    · linarith only [h404, h406, h414, h6, h9, hc13, hlam, hphi, u1ehi1]
                                    · rcases h5bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h404, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p416_1, u1ehi1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h404, h9, hc45, hlam, hphi, ht12, ht23, ht34, p416_1, u1ehi1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h414, h9, hc34, hc45, hlam, hphi, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h9, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h3, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h404, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h3, h414, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h408, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h6, hlam, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h4, h411, hc02, hc15, hlam, hphi, ht0b, ht5b, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h0, h4, h411, h414, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h412, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h8, hlam, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h407, hlam, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h411, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h414, hlam, p416_0]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h3, h404, hc45, hlam, hphi, ht12, ht23, ht34, p416_1, u1ehi1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h404, hc45, hlam, hphi, ht12, ht23, ht34, p416_1, u1ehi1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h404, hc45, hlam, hphi, ht12, ht23, ht34, p416_1, u1ehi1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [h414, hc34, hc45, hlam, hphi, p416_1]
                                      · have p416_0 := h416c.1
                                        have p416_1 := h416c.2.1
                                        have p416_2 := h416c.2.2.1
                                        have p416_3 := h416c.2.2.2
                                        linarith only [hlam, p416_0]
                                · linarith only [h0, h326, h4, h411, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h326, h410, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
                            · linarith only [h2, h444, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                                · linarith only [h407, h447, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h0, h326, h4, h447, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h326, h406, h446, hc13, hlam, hphi, u1ehi1]
                        · linarith only [h406, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h452 | h452
                  · linarith only [h452, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h455 | h455
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
                          · linarith only [h1, h457, h8, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h459 | h459
                            · linarith only [h2, h452, h459, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h461 | h461
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h462 | h462
                                · linarith only [h2, h454, h462, h7, h8, hc12, hlam, hphi, u1ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h464 | h464
                                  · linarith only [h2, h452, h464, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h466 | h466
                                    · linarith only [h1, h2, h452, h454, h461, h466, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                    · rcases h5bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p468_1, u1ehi4]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h0, h461, h462, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p468_1, u2ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h8, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h452, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h3, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h461, h462, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p468_1, u2ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h457, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h459, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h6, hlam, p468_1]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h455, hlam, p468_1]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h462, hlam, p468_1]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h464, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h3, h466, hc45, hlam, hphi, ht12, ht23, ht34, p468_1, u1ehi4]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h455, h461, h462, h466, hc45, hlam, hphi, ht23, ht34, p468_1, u2ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h461, h462, h466, hc45, hlam, hphi, ht23, ht34, p468_1, u2ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h466, hlam, p468_0]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h8, hc03, hc45, hlam, hphi, ht34, p468_1]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h455, h461, h462, hc45, hlam, hphi, ht23, ht34, p468_1, u2ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h461, h462, hc45, hlam, hphi, ht23, ht34, p468_1, u2ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [h2, h7, h8, hc45, hlam, hphi, ht12, ht23, ht34, p468_1, u1ehi3]
                                      · have p468_0 := h468c.1
                                        have p468_1 := h468c.2.1
                                        have p468_2 := h468c.2.2.1
                                        have p468_3 := h468c.2.2.2
                                        linarith only [hlam, p468_0]
                              · linarith only [h461, h7, h8, hc23, hc35, hlam, hphi]
                        · linarith only [h456, h7, h8, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h454, h455, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h4, h454, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h498 | h498
                · rcases m.htr 0 4 5 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
                        · linarith only [h1, h498, h502, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h504 | h504
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h505 | h505
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h506 | h506
                              · linarith only [h3, h498, h500, h506, h7, hc12, hlam, hphi, u1ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                                    · rcases h5bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [hlam, p511_0]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h498, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p511_1, u1ehi4]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h498, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h498, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h498, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h3, hlam, p511_0]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [hlam, p511_0]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h504, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p511_1, u2ehi4]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h1, h504, h510, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h1, h504, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h6, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h501, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [hlam, p511_0]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h0, h510, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h0, h500, h508, hc01, hc45, hlam, hphi, ht0b, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h498, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h504, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h508, hlam, p511_0]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [hlam, p511_0]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h498, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h499, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h505, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h509, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [h510, hlam, p511_1]
                                      · have p511_0 := h511c.1
                                        have p511_1 := h511c.2.1
                                        have p511_2 := h511c.2.2.1
                                        have p511_3 := h511c.2.2.2
                                        linarith only [hlam, p511_0]
                                    · linarith only [h1, h510, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                  · linarith only [h3, h498, h505, h506, h509, h7, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h498, h508, h7, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h499, h505, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h498, h504, h7, hc13, hc34, hlam, hphi]
                      · linarith only [h500, h501, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h4, h500, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h498, h499, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                        · linarith only [h1, h548, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                          · linarith only [h1, h498, h550, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                              · linarith only [h1, h546, h553, h7, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                                · linarith only [h1, h498, h546, h555, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                                    · rcases h5bigk with h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h545, h550, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p559_1, u1ehi2]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h0, h5, h545, h555, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p559_1, u2ehi2]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h498, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        rcases p559_3 (m.d 0 5) (by simp) with h564 | h564
                                        · rcases p559_3 (m.d 1 5) (by simp) with h565 | h565
                                          · linarith only [h3, h565, hlam]
                                          · linarith only [h552, h565, hlam]
                                        · linarith only [h545, h564, hlam]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h3, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h552, h555, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p559_1, u2ehi2]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h550, hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h2, h552, hc01, hc45, hlam, hphi, ht0b, ht5b, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h6, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h547, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h555, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h0, h5, h557, hc01, hc45, hlam, hphi, ht0b, ht5b, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h3, hc35, hlam, hphi, ht12, ht23, p559_1, u1ehi4]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht12, ht23, p559_1, u1ehi4]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hc35, hlam, hphi, ht23, p559_1, u2ehi4]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        rcases p559_3 (m.d 0 5) (by simp) with h583 | h583
                                        · linarith only [h498, h583, hlam]
                                        · linarith only [h545, h583, hlam]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h545, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h552, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h557, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [h558, hlam, p559_1]
                                      · have p559_0 := h559c.1
                                        have p559_1 := h559c.2.1
                                        have p559_2 := h559c.2.2.1
                                        have p559_3 := h559c.2.2.2
                                        linarith only [hlam, p559_0]
                                    · linarith only [h1, h558, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                                  · linarith only [h545, h557, h7, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h545, h552, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · linarith only [h546, h547, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h4, h546, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h596 | h596
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h598 | h598
                        · linarith only [h1, h598, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h600 | h600
                          · linarith only [h1, h498, h600, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h602 | h602
                            · linarith only [h2, h545, h602, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                              · linarith only [h1, h604, h7, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                                · linarith only [h1, h498, h596, h606, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h608 | h608
                                  · linarith only [h1, h545, h608, h7, hc24, hlam, hphi, ht12, u1ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h610 | h610
                                    · linarith only [h1, h545, h610, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                    · linarith only [h1, h610, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h0, h596, h597, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h4, h596, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h617 | h617
          · linarith only [h4, h617, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h619 | h619
            · linarith only [h4, h619, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h621 | h621
              · rcases m.htr 0 3 5 (by decide) (by decide) with h622 | h622
                · rcases m.htr 0 4 5 (by decide) (by decide) with h623 | h623
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
                    · linarith only [h0, h4, h624, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h626 | h626
                      · linarith only [h0, h619, h626, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h629 | h629
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h630 | h630
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h631 | h631
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h632 | h632
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h633 | h633
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h634 | h634
                                    · rcases h5bigk with h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c | h635c
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h621, h623, h626, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p635_1, u1ehi1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h619, hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        rcases p635_3 (m.d 0 5) (by simp) with h639 | h639
                                        · rcases p635_3 (m.d 1 5) (by simp) with h640 | h640
                                          · linarith only [h3, h640, hlam]
                                          · linarith only [h629, h640, hlam]
                                        · linarith only [h622, h639, hlam]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        rcases p635_3 (m.d 0 5) (by simp) with h644 | h644
                                        · rcases p635_3 (m.d 1 5) (by simp) with h645 | h645
                                          · linarith only [h3, h645, hlam]
                                          · linarith only [h630, h645, hlam]
                                        · linarith only [h623, h644, hlam]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h3, hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h626, hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h2, h630, h634, hc01, hc45, hlam, hphi, ht0b, ht5b, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h1, h628, h630, hc01, hc45, hlam, hphi, ht0b, ht5b, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h3, hc25, hlam, hphi, ht12, p635_1, u1ehi4]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht12, p635_1, u1ehi4]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        rcases p635_3 (m.d 0 5) (by simp) with h657 | h657
                                        · linarith only [h619, h657, hlam]
                                        · linarith only [h622, h657, hlam]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        rcases p635_3 (m.d 0 5) (by simp) with h660 | h660
                                        · linarith only [h619, h660, hlam]
                                        · linarith only [h623, h660, hlam]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h622, hlam, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h629, hlam, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h632, hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [hlam, p635_0]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h622, hc03, hc45, hlam, hphi, ht0b, ht5b, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h623, hlam, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h630, hlam, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h633, hlam, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [h634, hlam, p635_1]
                                      · have p635_0 := h635c.1
                                        have p635_1 := h635c.2.1
                                        have p635_2 := h635c.2.2.1
                                        have p635_3 := h635c.2.2.2
                                        linarith only [hlam, p635_0]
                                    · rcases h5bigk with h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h626, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p673_1, u1ehi1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h619, hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        rcases p673_3 (m.d 0 5) (by simp) with h677 | h677
                                        · rcases p673_3 (m.d 1 5) (by simp) with h678 | h678
                                          · linarith only [h3, h678, hlam]
                                          · linarith only [h629, h678, hlam]
                                        · linarith only [h622, h677, hlam]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h619, h631, h633, h634, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h3, hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h626, hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h1, h628, h630, h634, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h3, h631, h633, hc23, hlam, hphi, ht12, p673_1, u1ehi4]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h631, h633, hc23, hlam, hphi, ht12, p673_1, u1ehi4]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        rcases p673_3 (m.d 0 5) (by simp) with h691 | h691
                                        · linarith only [h619, h691, hlam]
                                        · linarith only [h622, h691, hlam]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h631, h633, h634, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h622, hlam, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h629, hlam, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h632, hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h634, hlam, p673_0]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h623, hlam, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h630, hlam, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h633, hlam, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [h634, hc34, hc45, hlam, hphi, p673_1]
                                      · have p673_0 := h673c.1
                                        have p673_1 := h673c.2.1
                                        have p673_2 := h673c.2.2.1
                                        have p673_3 := h673c.2.2.2
                                        linarith only [hlam, p673_0]
                                  · linarith only [h1, h628, h630, h633, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h4, h632, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h4, h631, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h617, h623, h630, hc24, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h4, h622, h629, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h4, h621, h624, h628, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
                    · linarith only [h0, h4, h711, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h713 | h713
                      · linarith only [h0, h619, h713, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h715 | h715
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h716 | h716
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
                            · linarith only [h2, h623, h717, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h719 | h719
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h720 | h720
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h721 | h721
                                  · linarith only [h0, h617, h623, h719, h721, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h617, h721, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h1, h716, h720, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h4, h719, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h4, h622, h716, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h4, h621, h711, h715, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h728 | h728
                  · linarith only [h621, h622, h728, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                    · linarith only [h0, h617, h730, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                      · linarith only [h0, h619, h732, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h734 | h734
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h735 | h735
                          · linarith only [h1, h622, h735, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h737 | h737
                            · linarith only [h2, h728, h737, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h739 | h739
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h740 | h740
                                · linarith only [h1, h622, h740, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h0, h4, h740, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h4, h739, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h4, h621, h730, h734, hc23, hlam, hphi, ht12, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h745 | h745
                · rcases m.htr 0 4 5 (by decide) (by decide) with h746 | h746
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
                    · linarith only [h0, h617, h747, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h749 | h749
                      · linarith only [h0, h619, h621, h745, h749, hc34, hlam, hphi, ht23, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h751 | h751
                        · linarith only [h1, h621, h751, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h754 | h754
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h755 | h755
                              · linarith only [h619, h621, h745, h755, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h0, h4, h755, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h617, h746, h751, h754, hc24, hlam, hphi, ht12, u1ehi2]
                          · linarith only [h4, h745, h747, h753, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h621, h745, h746, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h761 | h761
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h762 | h762
                    · linarith only [h0, h619, h762, hc25, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h764 | h764
                      · linarith only [h0, h4, h745, h764, hc35, hlam, hphi, ht23, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h766 | h766
                        · linarith only [h1, h4, h621, h766, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h768 | h768
                          · linarith only [h1, h745, h768, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h770 | h770
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h771 | h771
                              · linarith only [h0, h4, h621, h771, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h771, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h617, h761, h770, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
                    · linarith only [h0, h4, h775, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
                      · linarith only [h0, h4, h621, h761, h777, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
                        · linarith only [h1, h621, h779, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h781 | h781
                          · linarith only [h1, h745, h781, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h783 | h783
                            · linarith only [h0, h4, h621, h761, h783, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h785 | h785
                              · linarith only [h0, h4, h621, h785, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h785, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

end R2N4
