import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
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
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                            · rcases h5bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h2, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h2, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h2, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h5, hlam, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h11, hlam, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h5, hc02, hc35, hlam, hphi, ht0b, ht5b, p19_1]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h11, h2, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h7, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h13, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h16, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19_1, u3elo4]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h8, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h14, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h17, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [h18, hlam, p19_0]
                              · have p19_0 := h19c.1
                                have p19_1 := h19c.2.1
                                have p19_2 := h19c.2.2.1
                                have p19_3 := h19c.2.2.2
                                linarith only [hlam, p19_0]
                            · rcases h5bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h2, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p45_1]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h2, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h2, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h5, hlam, p45_1]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h11, hlam, p45_1]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h5, hc02, hc35, hlam, hphi, ht0b, ht5b, p45_1]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h11, h2, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h7, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h13, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h16, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h18, hlam, p45_1]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h8, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h14, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h17, hlam, p45_0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u3elo0]
                              · have p45_0 := h45c.1
                                have p45_1 := h45c.2.1
                                have p45_2 := h45c.2.2.1
                                have p45_3 := h45c.2.2.2
                                linarith only [hlam, p45_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                            · linarith only [h17, h6, h71, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases h5bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h6, h71, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h15, h17, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h2, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h2, h6, h71, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h15, h17, h2, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h5, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h11, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h5, h71, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h17, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h7, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h13, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h16, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h71, hlam, p73_1]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h8, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h14, hlam, p73_0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [h1, h14, h6, h71, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p73_1, u3elo0]
                              · have p73_0 := h73c.1
                                have p73_1 := h73c.2.1
                                have p73_2 := h73c.2.2.1
                                have p73_3 := h73c.2.2.2
                                linarith only [hlam, p73_0]
                        · linarith only [h16, h7, hc23, hlam, hphi, u3elo0]
                      · linarith only [h15, h6, hc23, hlam, hphi, u3elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                          · linarith only [h10, h103, h14, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                            · linarith only [h101, h105, h14, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases h5bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h10, h101, h14, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h2, hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h102, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h2, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h14, hlam, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h5, hlam, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h11, hlam, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h5, hc02, hc35, hlam, hphi, ht0b, ht5b, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h103, hlam, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h7, hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h13, hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h102, hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h105, hlam, p107_1]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h8, hlam, p107_0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h11, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h102, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p107_1, u3elo0]
                              · have p107_0 := h107c.1
                                have p107_1 := h107c.2.1
                                have p107_2 := h107c.2.2.1
                                have p107_3 := h107c.2.2.2
                                linarith only [hlam, p107_0]
                        · linarith only [h102, h7, hc23, hlam, hphi, u3elo0]
                      · linarith only [h101, h6, hc23, hlam, hphi, u3elo0]
                  · linarith only [h13, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h12, h6, h9, hc23, hlam, hphi, u3elo0]
              · linarith only [h11, h5, h6, h8, h9, hc23, hlam, hphi, u3elo0]
            · linarith only [h10, h4, h6, h9, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
              · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h143 | h143
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h145 | h145
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                          · linarith only [h139, h146, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · linarith only [h139, h143, h146, h3, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h145, h9, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h144, h9, hc12, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                          · linarith only [h139, h143, h153, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                            · linarith only [h139, h143, h151, h155, hlam]
                            · rcases h5bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h139, h143, h151, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h151, h153, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h155, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h139, h143, h151, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h2, hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h151, h153, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h140, h155, h3, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h143, hlam, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h5, hlam, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h140, hlam, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h155, h5, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h153, hlam, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h7, hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h142, hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h152, hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h155, hlam, p157_1]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h8, hlam, p157_0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h152, h155, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [h155, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p157_1, u3elo0]
                              · have p157_0 := h157c.1
                                have p157_1 := h157c.2.1
                                have p157_2 := h157c.2.2.1
                                have p157_3 := h157c.2.2.2
                                linarith only [hlam, p157_0]
                        · linarith only [h152, h9, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h139, h151, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h142, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h139, h141, h6, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                · rcases m.htr 1 3 5 (by decide) (by decide) with h188 | h188
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                    · linarith only [h139, h140, h189, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
                          · linarith only [h139, h140, h189, h192, h193, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h140, h193, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h188, h189, h192, h6, h8, h9, hc13, hlam, hphi, u3elo0]
                      · linarith only [h191, h9, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h188, h7, h9, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h139, h187, h6, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h200 | h200
              · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 3 5 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h207 | h207
                            · rcases h5bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h205, h207, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h207, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h2, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h2, h205, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h139, h200, h207, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p208_1]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h139, h200, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h5, hlam, p208_1]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h200, hlam, p208_1]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h207, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h139, h200, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h7, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h202, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h205, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p208_1, u3elo4]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h8, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h203, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h206, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [h207, hlam, p208_0]
                              · have p208_0 := h208c.1
                                have p208_1 := h208c.2.1
                                have p208_2 := h208c.2.2.1
                                have p208_3 := h208c.2.2.2
                                linarith only [hlam, p208_0]
                            · linarith only [h139, h200, h206, h207, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h139, h200, h201, h203, h206, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h205, h7, h9, hc13, hlam, hphi, u3elo0]
                      · linarith only [h200, h204, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h139, h200, h203, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                  · linarith only [h139, h200, h201, h202, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                · linarith only [h201, h6, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h243 | h243
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                            · rcases h5bigk with h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h200, h6, h8, hc12, hlam, hphi, ht23, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h2, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h200, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p248_1]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h139, h243, h244, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo2]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h5, hlam, p248_1]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h5, h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h5, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h5, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h7, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h242, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h245, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p248_1, u3elo4]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h8, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h243, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h246, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [h247, hlam, p248_0]
                              · have p248_0 := h248c.1
                                have p248_1 := h248c.2.1
                                have p248_2 := h248c.2.2.1
                                have p248_3 := h248c.2.2.2
                                linarith only [hlam, p248_0]
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
                                linarith only [h243, h247, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h247, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h2, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h200, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p274_1]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h200, h247, h5, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h5, hlam, p274_1]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h5, h6, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h5, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h247, h5, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p274_1, u3elo0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h7, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h242, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h245, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h247, hlam, p274_1]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h8, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h243, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h246, hlam, p274_0]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [h2, h243, hc01, hc35, hlam, hphi, ht0b, ht5b, p274_1]
                              · have p274_0 := h274c.1
                                have p274_1 := h274c.2.1
                                have p274_2 := h274c.2.2.1
                                have p274_3 := h274c.2.2.2
                                linarith only [hlam, p274_0]
                          · linarith only [h139, h241, h243, h246, h3, h9, hc12, hlam, hphi, ht23, u3elo0]
                        · linarith only [h245, h7, h9, hc13, hlam, hphi, u3elo0]
                      · linarith only [h244, h9, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h139, h243, h6, h8, hc12, hlam, hphi, ht23, u3elo0]
                  · linarith only [h242, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h241, h6, h9, hc12, hlam, hphi, ht23, u3elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h306 | h306
          · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
            · rcases m.htr 1 2 5 (by decide) (by decide) with h308 | h308
              · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
                · rcases m.htr 1 3 5 (by decide) (by decide) with h310 | h310
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h311 | h311
                    · linarith only [h1, h311, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h313 | h313
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h314 | h314
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h315 | h315
                          · linarith only [h1, h307, h315, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h317 | h317
                            · linarith only [h0, h306, h313, h317, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases h5bigk with h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c | h319c
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h7, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p319_1, u3elo0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p319_1, u3elo0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p319_1, u3elo0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h8, hlam, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h2, hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h2, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p319_1, u3elo0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h311, hlam, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h5, hlam, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h308, hlam, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h5, hc02, hc35, hlam, hphi, ht0b, ht5b, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h315, hlam, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h7, hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h310, hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h314, hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [hlam, p319_0]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h317, hlam, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h1, h307, h313, h8, hc34, hc45, hlam, hphi, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h307, h311, h313, hc34, hc45, hlam, hphi, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h313, h315, hc34, hc45, hlam, hphi, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [h317, hc34, hc45, hlam, hphi, p319_1]
                              · have p319_0 := h319c.1
                                have p319_1 := h319c.2.1
                                have p319_2 := h319c.2.2.1
                                have p319_3 := h319c.2.2.2
                                linarith only [hlam, p319_0]
                        · linarith only [h314, h7, hc23, hlam, hphi, u3elo0]
                      · linarith only [h313, h6, hc23, hlam, hphi, u3elo0]
                  · linarith only [h310, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h306, h309, h6, hc23, hlam, hphi, u3elo0]
              · linarith only [h306, h308, h5, h7, hc23, hlam, hphi, u3elo0]
            · linarith only [h306, h307, h4, h7, h8, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h351 | h351
            · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
              · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
                · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                    · linarith only [h3, h306, h351, h355, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h358 | h358
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h359 | h359
                          · linarith only [h1, h351, h359, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h361 | h361
                            · linarith only [h1, h351, h357, h361, h8, hlam]
                            · rcases h5bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h355, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p363_1, u3elo0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h357, h359, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p363_1, u3elo0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h361, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p363_1, u3elo0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h8, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h2, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h2, h357, h359, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h2, h361, h8, hc34, hc45, hlam, hphi, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h355, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h5, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h352, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h3, h306, h352, h361, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h359, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h7, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h354, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h358, hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h361, hlam, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h361, h7, hc34, hc45, hlam, hphi, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h354, h361, hc34, hc45, hlam, hphi, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h358, h361, hc34, hc45, hlam, hphi, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [h361, hc34, hc45, hlam, hphi, p363_1]
                              · have p363_0 := h363c.1
                                have p363_1 := h363c.2.1
                                have p363_2 := h363c.2.2.1
                                have p363_3 := h363c.2.2.2
                                linarith only [hlam, p363_0]
                        · linarith only [h306, h358, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h306, h351, h357, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h306, h354, h7, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h306, h351, h353, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
                · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                    · linarith only [h1, h395, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
                          · linarith only [h351, h352, h399, h5, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h401 | h401
                            · linarith only [h351, h352, h397, h401, h5, h8, hlam]
                            · rcases h5bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h351, h352, h397, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p403_1, u3elo0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h351, h352, h397, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p403_1, u3elo0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p403_1, u3elo0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h8, hlam, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h2, hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h352, hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h394, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p403_1, u3elo1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h395, hlam, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h5, hlam, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h5, hc02, hc15, hlam, hphi, ht0b, ht5b, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p403_1, u3elo0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h399, hlam, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h7, hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h394, hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h398, hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [hlam, p403_0]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h401, hlam, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h2, h351, h352, h397, hc34, hc45, hlam, hphi, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h351, h352, h397, hc34, hc45, hlam, hphi, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h351, h352, h397, hc34, hc45, hlam, hphi, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [h401, hc34, hc45, hlam, hphi, p403_1]
                              · have p403_0 := h403c.1
                                have p403_1 := h403c.2.1
                                have p403_2 := h403c.2.2.1
                                have p403_3 := h403c.2.2.2
                                linarith only [hlam, p403_0]
                        · linarith only [h306, h398, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h306, h397, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h394, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h306, h351, h393, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
              · rcases m.htr 1 3 4 (by decide) (by decide) with h434 | h434
                · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h436 | h436
                    · linarith only [h351, h4, h434, h436, h8, hc12, hlam, hphi, ht23, u3elo1]
                    · linarith only [h351, h433, h436, hlam]
                  · linarith only [h435, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h306, h433, h434, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h441 | h441
                · rcases m.htr 1 3 5 (by decide) (by decide) with h442 | h442
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h443 | h443
                    · linarith only [h1, h443, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h446 | h446
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                          · linarith only [h4, h447, h8, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
                            · linarith only [h351, h4, h441, h449, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases h5bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h443, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p451_1, u3elo0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h351, h447, h7, hc12, hlam, hphi, ht23, p451_1, u3elo0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1, u3elo0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h8, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h2, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h433, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h443, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h5, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h5, hc02, hc15, hlam, hphi, ht0b, ht5b, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1, u3elo0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h447, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h7, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h442, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h446, hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h449, hlam, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h2, h351, h443, hc12, hc45, hlam, hphi, ht23, ht34, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h351, h443, hc12, hc45, hlam, hphi, ht23, ht34, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h433, hc12, hc45, hlam, hphi, ht23, ht34, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [h449, hc34, hc45, hlam, hphi, p451_1]
                              · have p451_0 := h451c.1
                                have p451_1 := h451c.2.1
                                have p451_2 := h451c.2.2.1
                                have p451_3 := h451c.2.2.2
                                linarith only [hlam, p451_0]
                        · linarith only [h306, h446, h7, hc13, hlam, hphi, u3elo0]
                      · linarith only [h306, h445, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h442, h7, hc13, hlam, hphi, u3elo0]
                · linarith only [h306, h441, h6, hc12, hlam, hphi, ht23, u3elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
        · linarith only [h481, h6, h7, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
          · rcases m.htr 1 2 4 (by decide) (by decide) with h484 | h484
            · rcases m.htr 1 2 5 (by decide) (by decide) with h485 | h485
              · rcases m.htr 1 3 4 (by decide) (by decide) with h486 | h486
                · rcases m.htr 1 3 5 (by decide) (by decide) with h487 | h487
                  · linarith only [h0, h487, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h1, h481, h489, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h492 | h492
                        · linarith only [h0, h483, h492, h7, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
                          · linarith only [h1, h481, h484, h494, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h481, h485, h491, h492, h496, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h5bigk with h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c | h498c
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h485, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo4]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo4]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h7, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h481, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h2, hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h487, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h489, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h5, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h485, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h492, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h494, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo4]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo4]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p498_1, u3elo4]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h496, hlam, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h2, h487, hc13, hc45, hlam, hphi, ht34, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h486, h487, hc34, hc45, hlam, hphi, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h491, h492, hc34, hc45, hlam, hphi, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [h0, h483, h491, h7, hc34, hc45, hlam, hphi, p498_1]
                              · have p498_0 := h498c.1
                                have p498_1 := h498c.2.1
                                have p498_2 := h498c.2.2.1
                                have p498_3 := h498c.2.2.2
                                linarith only [hlam, p498_0]
                      · linarith only [h491, h6, h7, hc23, hlam, hphi, u3elo4]
                · linarith only [h486, h6, h7, hc13, hlam, hphi, u3elo4]
              · linarith only [h483, h485, h5, h7, hc23, hlam, hphi, u3elo4]
            · linarith only [h4, h483, h484, h6, h7, hc23, hlam, hphi, u3elo4]
          · linarith only [h3, h483, h7, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h529 | h529
      · rcases m.htr 0 4 5 (by decide) (by decide) with h530 | h530
        · rcases m.htr 1 2 3 (by decide) (by decide) with h531 | h531
          · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
            · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
              · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
                · linarith only [h0, h534, h6, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                      · linarith only [h0, h531, h538, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h541 | h541
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h542 | h542
                            · rcases h5bigk with h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c | h543c
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h529, h533, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h529, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h529, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h529, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h2, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p543_1]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h2, h529, h542, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h2, h529, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h5, hlam, p543_1]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h533, hlam, p543_1]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h5, h542, hc02, hc45, hlam, hphi, ht0b, ht5b, p543_1]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h2, h529, h533, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo3]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h529, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h536, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h540, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p543_1, u3elo4]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h530, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h537, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h541, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [h542, hlam, p543_0]
                              · have p543_0 := h543c.1
                                have p543_1 := h543c.2.1
                                have p543_2 := h543c.2.2.1
                                have p543_3 := h543c.2.2.2
                                linarith only [hlam, p543_0]
                            · linarith only [h0, h530, h531, h540, h542, h6, hc04, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h2, h529, h537, h538, h541, h6, hc23, hlam, hphi, u3elo3]
                        · linarith only [h529, h540, h6, hc23, hlam, hphi, u3elo3]
                    · linarith only [h529, h530, h534, h537, h6, hc13, hlam, hphi, u3elo3]
                  · linarith only [h529, h531, h536, h6, hc23, hlam, hphi, u3elo3]
              · linarith only [h5, h529, h533, h6, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h4, h531, h532, h6, hc23, hlam, hphi, u3elo3]
          · linarith only [h3, h531, h6, hc12, hlam, hphi, ht23, u3elo3]
        · linarith only [h529, h530, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
        · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
          · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
            · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
              · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
                · linarith only [h0, h582, h6, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h584 | h584
                  · linarith only [h0, h529, h584, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h586 | h586
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h587 | h587
                      · linarith only [h0, h579, h587, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h589 | h589
                        · linarith only [h0, h529, h579, h589, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h591 | h591
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h592 | h592
                            · rcases h5bigk with h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h578, h584, h6, hc13, hlam, hphi, p593_1, u3elo3]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h578, h589, h6, hc23, hlam, hphi, p593_1, u3elo3]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h529, hlam, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h529, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p593_1, u3elo4]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h2, hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h2, h589, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h584, hlam, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h1, h586, hc01, hc45, hlam, hphi, ht0b, ht5b, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h5, hlam, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h581, hlam, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h589, hlam, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p593_1]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p593_1, u3elo4]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p593_1, u3elo4]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p593_1, u3elo4]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h592, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p593_1, u3elo3]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h578, hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h586, hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h591, hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [h592, hlam, p593_0]
                              · have p593_0 := h593c.1
                                have p593_1 := h593c.2.1
                                have p593_2 := h593c.2.2.1
                                have p593_3 := h593c.2.2.2
                                linarith only [hlam, p593_0]
                            · linarith only [h4, h591, h592, h6, hlam]
                          · linarith only [h1, h586, h587, h591, h6, hc23, hlam, hphi, u3elo3]
                    · linarith only [h578, h579, h582, h586, h6, hc23, hlam, hphi, u3elo3]
              · linarith only [h5, h529, h579, h581, hc23, hlam, hphi, u3elo4]
            · linarith only [h4, h579, h580, h6, hc23, hlam, hphi, u3elo3]
          · linarith only [h3, h579, h6, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h625 | h625
          · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
            · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                · linarith only [h0, h6, h628, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h630 | h630
                  · linarith only [h1, h529, h578, h628, h630, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h632 | h632
                    · linarith only [h1, h578, h632, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                      · linarith only [h0, h6, h625, h634, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                        · linarith only [h0, h529, h625, h636, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                          · linarith only [h4, h578, h638, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h640 | h640
                            · linarith only [h0, h578, h6, h625, h640, hc23, hlam, hphi, u3elo3]
                            · rcases h5bigk with h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c | h642c
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [hlam, p642_0]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h529, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p642_1, u3elo4]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h529, h638, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p642_1, u3elo4]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h529, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h578, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h2, hlam, p642_0]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [hlam, p642_0]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h2, h638, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h630, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h632, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h5, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h627, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [hlam, p642_0]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h636, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h638, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p642_1, u3elo4]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h627, h638, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p642_1, u3elo4]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h634, h638, hc23, hlam, hphi, p642_1, u3elo4]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [hlam, p642_0]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h640, hlam, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h0, h578, h6, h625, hc23, hc45, hlam, hphi, ht34, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h625, h628, h632, hc23, hc45, hlam, hphi, ht34, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h634, h638, hc23, hc45, hlam, hphi, ht34, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [h0, h529, h625, hc23, hc45, hlam, hphi, ht34, p642_1]
                              · have p642_0 := h642c.1
                                have p642_1 := h642c.2.1
                                have p642_2 := h642c.2.2.1
                                have p642_3 := h642c.2.2.2
                                linarith only [hlam, p642_0]
              · linarith only [h5, h529, h625, h627, hc23, hlam, hphi, u3elo4]
            · linarith only [h4, h6, h625, h626, hc23, hlam, hphi, u3elo3]
          · linarith only [h3, h6, h625, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h671 | h671
    · rcases m.htr 0 3 5 (by decide) (by decide) with h672 | h672
      · linarith only [h3, h5, h672, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h674 | h674
        · linarith only [h3, h5, h671, h674, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
          · rcases m.htr 1 2 4 (by decide) (by decide) with h677 | h677
            · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
              · linarith only [h2, h5, h678, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h680 | h680
                · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
                  · linarith only [h0, h672, h681, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h683 | h683
                    · linarith only [h1, h2, h671, h672, h674, h678, h683, hc12, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h686 | h686
                        · linarith only [h672, h686, hc03, hlam, hphi, u3elo2]
                        · linarith only [h3, h5, h686, hc23, hlam, hphi, u3elo4]
                      · linarith only [h680, h685, hc23, hlam, hphi, u3elo1]
                · linarith only [h671, h672, h680, hc13, hlam, hphi, u3elo4]
            · linarith only [h4, h5, h677, hc12, hc25, hlam, hphi]
          · linarith only [h3, h5, h672, h676, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h693 | h693
      · linarith only [h3, h5, h671, h693, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h695 | h695
        · linarith only [h4, h5, h695, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h697 | h697
          · rcases m.htr 1 2 4 (by decide) (by decide) with h698 | h698
            · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
              · linarith only [h2, h5, h699, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                · linarith only [h671, h701, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h703 | h703
                  · linarith only [h0, h2, h671, h693, h699, h703, hc12, hlam, hphi, ht23, u3elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h705 | h705
                    · linarith only [h1, h695, h705, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h707 | h707
                      · linarith only [h2, h671, h697, h699, h707, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h709 | h709
                        · linarith only [h3, h5, h693, h709, hlam]
                        · linarith only [h3, h5, h709, hc23, hlam, hphi, u3elo4]
            · linarith only [h4, h5, h698, hc12, hc25, hlam, hphi]
          · linarith only [h3, h5, h693, h697, hc12, hlam, hphi, ht23, u3elo4]

end R2N4
