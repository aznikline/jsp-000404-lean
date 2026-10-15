import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3626000 in
set_option maxHeartbeats 3626000 in
theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                            · rcases h0bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h11, h14, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, h1, h10, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h3, hlam, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, h1, h10, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h0, h2, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h1, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1, u3ehi0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h1, h2, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p15_1, u2ehi4]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h2, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h4, hlam, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h5, hlam, p15_0]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [h6, hlam, p15_1]
                              · have p15_0 := h15c.1
                                have p15_1 := h15c.2.1
                                have p15_2 := h15c.2.2.1
                                have p15_3 := h15c.2.2.2
                                linarith only [hlam, p15_0]
                            · linarith only [h1, h10, h14, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h10, h13, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h11, h12, h3, h5, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h11, h44, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                            · rcases h0bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u3ehi0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h1, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u3ehi3]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h4, h44, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, h1, h44, h47, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, h44, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h3, hlam, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h1, h3, h44, h47, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h0, h3, h44, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h1, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h1, h44, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h1, h44, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u2ehi2]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h2, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h4, hlam, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h5, hlam, p48_0]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [h6, hlam, p48_1]
                              · have p48_0 := h48c.1
                                have p48_1 := h48c.2.1
                                have p48_2 := h48c.2.2.1
                                have p48_3 := h48c.2.2.2
                                linarith only [hlam, p48_0]
                            · linarith only [h1, h10, h47, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h10, h46, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                          · linarith only [h0, h10, h7, h78, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                            · linarith only [h10, h7, h80, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h0bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h10, h5, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h10, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h10, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h10, h5, h6, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h10, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h10, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h3, hlam, p82_1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h10, h3, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h0, h10, h3, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h1, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u3ehi0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h1, h10, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi3]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h2, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h4, hlam, p82_1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h5, hlam, p82_0]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [h6, hlam, p82_1]
                              · have p82_0 := h82c.1
                                have p82_1 := h82c.2.1
                                have p82_2 := h82c.2.2.1
                                have p82_3 := h82c.2.2.2
                                linarith only [hlam, p82_0]
                        · linarith only [h0, h3, h5, h76, h77, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h10, h76, h9, hc45, hlam, hphi, ht34, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                      · linarith only [h0, h111, h3, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h111, h113, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h115 | h115
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                            · rcases h0bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h113, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h113, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h1, h115, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p117_1]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h113, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h0, hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h113, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h0, h113, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h0, h113, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h3, hlam, p117_1]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h0, h113, h3, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h0, h113, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h1, hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h1, h113, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h1, h113, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p117_1, u2ehi2]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h2, hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h4, hlam, p117_1]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h5, hlam, p117_0]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [h6, hlam, p117_1]
                              · have p117_0 := h117c.1
                                have p117_1 := h117c.2.1
                                have p117_2 := h117c.2.2.1
                                have p117_3 := h117c.2.2.2
                                linarith only [hlam, p117_0]
                            · linarith only [h116, h9, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h1, h110, h115, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h145 | h145
                      · linarith only [h145, h3, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                        · linarith only [h0, h145, h147, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
                          · linarith only [h110, h149, h7, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                            · linarith only [h110, h145, h151, h7, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1, h151, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h7, h8, hc25, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
                · linarith only [h155, h7, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                            · rcases h0bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p163_1, u3ehi0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p163_1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h155, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p163_1, u3ehi0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, h155, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, h155, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h3, hlam, p163_1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, h155, h3, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h0, h155, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h1, hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p163_1, u3ehi0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h1, h155, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p163_1, u2ehi1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h2, hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h4, hlam, p163_1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h5, hlam, p163_0]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [h6, hlam, p163_1]
                              · have p163_0 := h163c.1
                                have p163_1 := h163c.2.1
                                have p163_2 := h163c.2.2.1
                                have p163_3 := h163c.2.2.2
                                linarith only [hlam, p163_0]
                            · linarith only [h0, h158, h159, h162, h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h158, h161, h7, hlam]
                        · linarith only [h0, h159, h160, h3, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · linarith only [h157, h159, h7, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                          · linarith only [h158, h195, h7, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h1, h195, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                        · linarith only [h193, h194, h7, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h1, h157, h158, h193, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                      · linarith only [h157, h201, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h203 | h203
                        · linarith only [h201, h203, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h205 | h205
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                            · rcases h0bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h155, h203, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h155, h203, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h155, h203, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h155, h203, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h155, h203, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h3, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h155, h203, h3, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h0, h155, h203, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h1, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h1, h155, h203, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h1, h155, h203, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p207_1, u2ehi1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h2, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h4, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h5, hlam, p207_0]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [h6, hlam, p207_1]
                              · have p207_0 := h207c.1
                                have p207_1 := h207c.2.1
                                have p207_2 := h207c.2.2.1
                                have p207_3 := h207c.2.2.2
                                linarith only [hlam, p207_0]
                            · linarith only [h157, h206, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h1, h200, h205, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                      · linarith only [h0, h157, h235, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                        · linarith only [h235, h237, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                          · linarith only [h200, h239, h7, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h239, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
              · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
                · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                    · linarith only [h1, h245, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h248 | h248
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h249 | h249
                          · linarith only [h1, h242, h249, h6, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                            · linarith only [h1, h242, h247, h251, h6, hc23, hlam, hphi, u2ehi3]
                            · rcases h0bigk with h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p253_1, u3ehi0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h1, h242, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi4]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h0, hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h248, h251, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p253_1, u3ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h0, h1, h242, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h0, h1, h242, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h3, hlam, p253_1]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h0, h1, h242, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h0, h1, h242, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h1, hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h6, hc45, hlam, hphi, ht34, p253_1, u3ehi0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h6, hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h2, hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h4, hlam, p253_1]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h5, hlam, p253_0]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [h1, h242, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u2ehi3]
                              · have p253_0 := h253c.1
                                have p253_1 := h253c.2.1
                                have p253_2 := h253c.2.2.1
                                have p253_3 := h253c.2.2.2
                                linarith only [hlam, p253_0]
                        · linarith only [h0, h247, h248, h3, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h244, h247, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                    · linarith only [h1, h281, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                      · linarith only [h0, h244, h283, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h285 | h285
                        · linarith only [h283, h285, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                          · linarith only [h0, h242, h287, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                            · linarith only [h1, h242, h283, h289, h6, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h244, h289, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h242, h243, hc25, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h293 | h293
                · linarith only [h242, h293, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h296 | h296
                    · linarith only [h1, h296, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h299 | h299
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h300 | h300
                          · linarith only [h0, h293, h298, h3, h300, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h242, h300, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h298, h299, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h295, h298, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                    · linarith only [h1, h305, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                      · linarith only [h0, h295, h3, h307, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                        · linarith only [h307, h309, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
                          · linarith only [h309, h311, h5, h6, hc24, hlam, hphi, u2ehi2]
                          · linarith only [h242, h311, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h314 | h314
            · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
              · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h319 | h319
                      · linarith only [h3, h319, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h321 | h321
                        · linarith only [h315, h317, h319, h321, h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                            · rcases h0bigk with h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p325_1, u3ehi0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h1, h317, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p325_1, u3ehi3]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h321, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi2]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h0, hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi2]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h0, h1, h3, h317, h324, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi2]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h0, h2, h316, h321, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi2]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h3, hlam, p325_1]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h0, h315, h317, h324, h5, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b, p325_1]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h5, hlam, p325_1]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h1, hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p325_1, u3ehi0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi4]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h2, hlam, p325_0]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h4, hlam, p325_1]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h3, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi2]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [h314, hlam, p325_1]
                              · have p325_0 := h325c.1
                                have p325_1 := h325c.2.1
                                have p325_2 := h325c.2.2.1
                                have p325_3 := h325c.2.2.2
                                linarith only [hlam, p325_0]
                            · linarith only [h0, h315, h323, h324, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h315, h318, h323, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                      · linarith only [h3, h353, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h314, h317, h318, h353, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                      · linarith only [h0, h3, h317, h357, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h357, h359, h5, hc34, hlam, hphi, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h361 | h361
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h362 | h362
                            · rcases h0bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u3ehi0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h1, h316, h356, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi4]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h2, h316, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi4]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h0, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u3ehi0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h0, h1, h315, h361, hc01, hc45, hlam, hphi, ht0b, ht5b, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h0, h2, h316, h359, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi2]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h3, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h314, h5, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h5, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h1, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p363_1, u3ehi0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h1, h2, h316, h359, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi2]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h2, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h4, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h3, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p363_1, u2ehi2]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h314, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                            · linarith only [h317, h362, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h1, h356, h361, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h391 | h391
                      · linarith only [h0, h3, h317, h391, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h393 | h393
                        · linarith only [h1, h314, h315, h356, h391, h393, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                          · linarith only [h315, h356, h395, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h397 | h397
                            · linarith only [h315, h356, h391, h397, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1, h314, h317, h397, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h315, h316, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h401 | h401
                · linarith only [h315, h401, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h405 | h405
                      · linarith only [h3, h405, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h315, h403, h405, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
                      · linarith only [h3, h408, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h314, h403, h404, h408, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h411 | h411
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                      · linarith only [h3, h412, h5, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h414 | h414
                        · linarith only [h0, h3, h414, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h416 | h416
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
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
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi2]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, h401, h411, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h4, h401, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi1]
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
                                linarith only [h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi2]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h314, h4, h401, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h4, h401, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h314, h4, h401, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h5, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1, u3ehi0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, h4, h401, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h2, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h4, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p418_1, u2ehi2]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h314, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                            · linarith only [h1, h411, h417, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1, h411, h416, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                      · linarith only [h0, h3, h403, h446, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h448 | h448
                        · linarith only [h3, h448, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                          · linarith only [h315, h411, h450, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h1, h314, h315, h450, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h453 | h453
              · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
                · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h456 | h456
                    · linarith only [h1, h314, h456, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h458 | h458
                      · linarith only [h3, h458, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h314, h455, h458, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h461 | h461
                    · linarith only [h1, h314, h461, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                      · linarith only [h0, h3, h455, h463, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h465 | h465
                        · linarith only [h453, h463, h465, h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                          · linarith only [h0, h314, h453, h467, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h469 | h469
                            · linarith only [h1, h314, h453, h463, h469, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h455, h469, hc45, hlam, hphi, ht34, u3ehi1]
                · linarith only [h453, h454, hc25, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                · linarith only [h1, h314, h453, h473, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h475 | h475
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                    · linarith only [h1, h314, h476, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h478 | h478
                      · linarith only [h3, h478, h5, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h314, h475, h478, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h481 | h481
                    · linarith only [h1, h314, h481, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                      · linarith only [h0, h3, h475, h483, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                        · linarith only [h0, h3, h485, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                          · linarith only [h1, h314, h453, h487, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h453, h487, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · linarith only [h3, h4, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h491 | h491
        · linarith only [h3, h491, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h493 | h493
          · rcases m.htr 0 4 5 (by decide) (by decide) with h494 | h494
            · rcases m.htr 1 2 4 (by decide) (by decide) with h495 | h495
              · linarith only [h0, h3, h495, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
                · linarith only [h0, h491, h497, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h503 | h503
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
                            · rcases h0bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h493, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, u3ehi4]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, h491, h494, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, h491, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h3, hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h491, h494, hlam, p505_1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h491, hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, h3, h491, h494, hc23, hlam, hphi, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, h3, h491, hc23, hlam, hphi, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h1, hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, u3ehi0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, h1, h491, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h2, hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h493, hlam, p505_0]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [h494, hlam, p505_1]
                              · have p505_0 := h505c.1
                                have p505_1 := h505c.2.1
                                have p505_2 := h505c.2.2.1
                                have p505_3 := h505c.2.2.2
                                linarith only [hlam, p505_0]
                            · linarith only [h1, h500, h504, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h495, h500, h503, hlam]
                        · linarith only [h0, h3, h502, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h3, h493, h501, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h535 | h535
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h536 | h536
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h537 | h537
                          · linarith only [h495, h500, h537, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h491, h494, h495, h537, hc25, hlam, hphi, u2ehi1]
                        · linarith only [h0, h3, h536, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h3, h493, h494, h499, h500, h535, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h543 | h543
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h544 | h544
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h545 | h545
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h546 | h546
                            · rcases h0bigk with h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c | h547c
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h493, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1, u3ehi4]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h494, hc01, hc45, hlam, hphi, ht0b, ht5b, p547_1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, h491, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h3, hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h491, h494, hlam, p547_1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h491, hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, h3, hc23, hlam, hphi, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, h3, h491, h494, hc23, hlam, hphi, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, h3, h491, hc23, hlam, hphi, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h1, hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p547_1, u3ehi0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, h1, h491, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h2, hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p547_1, u2ehi1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h493, hlam, p547_0]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [h494, hlam, p547_1]
                              · have p547_0 := h547c.1
                                have p547_1 := h547c.2.1
                                have p547_2 := h547c.2.2.1
                                have p547_3 := h547c.2.2.2
                                linarith only [hlam, p547_0]
                            · linarith only [h499, h546, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h499, h542, h545, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h543, h544, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h3, h543, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h578 | h578
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h579 | h579
                          · linarith only [h495, h542, h579, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h495, h579, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h3, h578, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h3, h493, h494, h495, h542, h577, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h584 | h584
              · linarith only [h0, h3, h584, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h586 | h586
                · linarith only [h1, h491, h494, h584, h586, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h588 | h588
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h589 | h589
                    · linarith only [h1, h494, h589, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h591 | h591
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h592 | h592
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h593 | h593
                          · linarith only [h1, h494, h584, h593, hc24, hlam, hphi, u2ehi1]
                          · linarith only [h584, h593, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h3, h493, h592, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · linarith only [h0, h3, h591, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h598 | h598
                    · linarith only [h1, h494, h598, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h600 | h600
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h602 | h602
                          · linarith only [h1, h494, h584, h600, h602, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h584, h602, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h3, h601, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h3, h493, h600, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h607 | h607
            · rcases m.htr 1 2 4 (by decide) (by decide) with h608 | h608
              · linarith only [h0, h3, h608, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                · linarith only [h608, h610, hc24, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h613 | h613
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h614 | h614
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h615 | h615
                        · linarith only [h3, h493, h615, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h0, h3, h615, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h3, h614, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h619 | h619
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h620 | h620
                        · linarith only [h3, h493, h620, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h0, h3, h620, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h3, h619, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h624 | h624
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h625 | h625
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
                        · linarith only [h0, h3, h493, h626, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h612, h625, h626, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h0, h3, h625, hc34, hlam, hphi, ht23, u2ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h630 | h630
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h631 | h631
                        · linarith only [h0, h3, h493, h631, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h3, h631, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h3, h630, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
              · linarith only [h0, h3, h635, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                · linarith only [h1, h491, h607, h635, h637, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h640 | h640
                    · linarith only [h1, h607, h640, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h642 | h642
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                        · linarith only [h0, h3, h493, h643, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h0, h3, h643, hc35, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h0, h3, h642, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h647 | h647
                    · linarith only [h1, h607, h647, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h649 | h649
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h650 | h650
                        · linarith only [h0, h3, h493, h650, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h639, h649, h650, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h0, h3, h649, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h654 | h654
      · rcases m.htr 0 2 5 (by decide) (by decide) with h655 | h655
        · linarith only [h0, h2, h655, hlam]
        · linarith only [h654, h655, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h658 | h658
        · linarith only [h654, h658, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h660 | h660
          · rcases m.htr 0 4 5 (by decide) (by decide) with h661 | h661
            · linarith only [h1, h2, h661, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h663 | h663
              · linarith only [h0, h654, h663, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h665 | h665
                · linarith only [h1, h2, h658, h663, h665, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h2, h665, hc25, hlam, hphi, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h668 | h668
            · linarith only [h1, h2, h668, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h670 | h670
              · linarith only [h0, h2, h670, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                · linarith only [h1, h2, h670, h672, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · linarith only [h1, h2, h670, h672, hc25, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h675 | h675
    · rcases m.htr 0 2 3 (by decide) (by decide) with h676 | h676
      · rcases m.htr 0 2 5 (by decide) (by decide) with h677 | h677
        · rcases m.htr 0 3 5 (by decide) (by decide) with h678 | h678
          · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
            · rcases m.htr 1 2 4 (by decide) (by decide) with h680 | h680
              · linarith only [h0, h1, h680, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h680, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h676, h679, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h684 | h684
            · rcases m.htr 1 2 4 (by decide) (by decide) with h685 | h685
              · linarith only [h0, h1, h685, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h685, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h676, h684, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h676, h677, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h690 | h690
        · linarith only [h676, h690, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h692 | h692
          · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
            · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
              · linarith only [h0, h1, h694, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h694, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h693, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h698 | h698
            · rcases m.htr 1 2 4 (by decide) (by decide) with h699 | h699
              · linarith only [h0, h1, h699, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h699, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h698, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h703 | h703
      · rcases m.htr 0 2 5 (by decide) (by decide) with h704 | h704
        · linarith only [h0, h675, h704, hlam]
        · linarith only [h703, h704, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h707 | h707
        · linarith only [h703, h707, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h709 | h709
          · rcases m.htr 0 4 5 (by decide) (by decide) with h710 | h710
            · rcases m.htr 1 2 4 (by decide) (by decide) with h711 | h711
              · linarith only [h0, h1, h711, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h711, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h710, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
            · rcases m.htr 1 2 4 (by decide) (by decide) with h716 | h716
              · linarith only [h0, h1, h716, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h716, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h715, hc45, hlam, hphi, ht23, ht34, u2ehi1]

end R2N4
